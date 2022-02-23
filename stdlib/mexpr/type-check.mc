-- Type check MExpr terms, annotating AST nodes with the results.
--
-- The type system is based on FreezeML [1], and gives ML-style
-- type inference along with the expressive power of System F
-- with low syntactic overhead.
--
-- The implementation uses efficient side-effecting unification,
-- as described in [2]. The current implementation corresponds to
-- the sound but eager version described.
--
-- [1]: https://dl.acm.org/doi/abs/10.1145/3385412.3386003
-- [2]: http://okmij.org/ftp/ML/generalization.html.

include "ast.mc"
include "ast-builder.mc"
include "const-types.mc"
include "eq.mc"
include "math.mc"
include "pprint.mc"
include "seq.mc"

type TCEnv = {
  varEnv: Map Name Type,
  conEnv: Map Name Type,
  tyConEnv: Map Name Type,
  currentLvl: Level,
  disableRecordPolymorphism: Bool
}

let _tcEnvEmpty = {
  varEnv = mapEmpty nameCmp,
  conEnv = mapEmpty nameCmp,
  tyConEnv = mapEmpty nameCmp,
  currentLvl = 1,
  disableRecordPolymorphism = true
}

let _insertVar = lam name. lam ty. lam env : TCEnv.
  {env with varEnv = mapInsert name ty env.varEnv}

let _insertCon = lam name. lam ty. lam env : TCEnv.
  {env with conEnv = mapInsert name ty env.conEnv}

let _insertTyCon = lam name. lam ty. lam env : TCEnv.
  {env with tyConEnv = mapInsert name ty env.tyConEnv}

type UnifyEnv = {
  names: BiNameMap,
  tyConEnv: Map Name Type
}

let errInfo = ref (NoInfo ())

let unificationError =
  lam lhs. lam rhs.
  let msg = join [
    "Type check failed: unification failure\n",
    "LHS: ", lhs, "\n",
    "RHS: ", rhs, "\n"
  ] in
  infoErrorExit (deref errInfo) msg

let _type2str = use MExprPrettyPrint in
  type2str

let _fields2str = use RecordTypeAst in
  lam m.
  _type2str (TyRecord {info = NoInfo (), fields = m, labels = mapKeys m})

let _sort2str = use MExprPrettyPrint in
  getVarSortStringCode 0 pprintEnvEmpty

recursive let resolveAlias = use MExprAst in
  lam env : Map Name Type. lam ty.
  match ty with TyCon t then
    match mapLookup t.ident env with Some ty then resolveAlias env ty
    else ty
  else ty
end

----------------------
-- TYPE UNIFICATION --
----------------------

lang Unify = MExprAst
  -- Unify the types `ty1' and `ty2'. Modifies the types in place.
  sem unify (env : TCEnv) (ty1 : Type) =
  | ty2 ->
    let env : UnifyEnv = {names = biEmpty, tyConEnv = env.tyConEnv} in
    unifyTypes env (ty1, ty2)

  sem unifyTypes (env : UnifyEnv) =
  | (ty1, ty2) ->
    let resolve = compose (resolveAlias env.tyConEnv) resolveLink in
    unifyBase env (resolve ty1, resolve ty2)

  -- Unify the types `ty1' and `ty2' under the assumptions of `env'.
  sem unifyBase (env : UnifyEnv) =
  | (ty1, ty2) ->
    unificationError (_type2str ty1) (_type2str ty2)

  -- checkBeforeUnify is called before a variable `tv' is unified with another type.
  -- Performs three tasks in one traversal:
  -- - Occurs check
  -- - Update level fields of FlexVars
  -- - If `tv' is monomorphic, ensure it is not unified with a polymorphic type
  sem checkBeforeUnify (tv : FlexVarRec) =
  | ty ->
    sfold_Type_Type (lam. lam ty. checkBeforeUnify tv ty) () ty
end

-- Helper language providing functions to unify fields of record-like types
lang UnifyFields = Unify
  -- Check that 'm1' is a subset of 'm2'
  sem unifyFields (env : UnifyEnv) (m1 : Map SID Type) =
  | m2 ->
    let f = lam b : (SID, Type).
      match b with (k, tyfield1) in
      match mapLookup k m2 with Some tyfield2 then
        unifyTypes env (tyfield1, tyfield2)
      else
        unificationError (_fields2str m1) (_fields2str m2)
    in
    iter f (mapBindings m1)

  -- Check that 'm1' and 'm2' contain the same fields
  sem unifyFieldsStrict (env : UnifyEnv) (m1 : Map SID Type) =
  | m2 ->
    if eqi (mapSize m1) (mapSize m2) then
      unifyFields env m1 m2
    else
      unificationError (_fields2str m1) (_fields2str m2)
end

lang VarTypeUnify = Unify + VarTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyVar t1 & ty1, TyVar t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else if biMem (t1.ident, t2.ident) env.names then ()
    else unificationError (_type2str ty1) (_type2str ty2)
end

lang FlexTypeUnify = UnifyFields + FlexTypeAst + UnknownTypeAst
  sem addSorts (env : UnifyEnv) =
  | (RecordVar r1, RecordVar r2) ->
    let f = lam acc. lam b : (SID, Type).
      match b with (k, ty2) in
      match mapLookup k r1.fields with Some ty1 then
        unifyTypes env (ty1, ty2);
        acc
      else
        mapInsert k ty2 acc
    in
    let fields = foldl f r1.fields (mapBindings r2.fields) in
    RecordVar {r1 with fields = fields}
  | (RecordVar _ & rv, ! RecordVar _ & tv)
  | (! RecordVar _ & tv, RecordVar _ & rv) ->
    rv
  | (TypeVar _, TypeVar _) -> TypeVar ()
  | (s1, s2) -> WeakVar ()

  sem unifyBase (env : UnifyEnv) =
  | (TyFlex t1 & ty1, TyFlex t2 & ty2) ->
    -- NOTE(aathn, 2021-11-17): unifyBase is always called by unifyTypes, which
    -- resolves any potential links, so TyFlexes are always unbound here.
    match (deref t1.contents, deref t2.contents) with (Unbound r1, Unbound r2) in
    if not (nameEq r1.ident r2.ident) then
      checkBeforeUnify r1 ty2;
      let updated =
        Unbound {{r1 with level = mini r1.level r2.level}
                     with sort = addSorts env (r1.sort, r2.sort)} in
      modref t1.contents updated;
      modref t2.contents (Link ty1)
    else ()
  | (TyFlex t1 & ty1, !(TyUnknown _ | TyFlex _) & ty2)
  | (!(TyUnknown _ | TyFlex _) & ty2, TyFlex t1 & ty1) ->
    match deref t1.contents with Unbound tv in
    checkBeforeUnify tv ty2;
    (match (tv.sort, ty2) with (RecordVar r1, TyRecord r2) then
       unifyFields env r1.fields r2.fields
     else match tv.sort with RecordVar _ then
       unificationError (_type2str ty1) (_type2str ty2)
     else ());
    modref t1.contents (Link ty2)

  sem checkBeforeUnify (tv : FlexVarRec) =
  | TyFlex t & ty ->
    match deref t.contents with Unbound r then
      if nameEq r.ident tv.ident then
        let msg = "Type check failed: occurs check\n" in
        infoErrorExit (deref errInfo) msg
      else
        let sort =
          match (tv.sort, r.sort) with (WeakVar _, TypeVar _) then WeakVar ()
          else
            sfold_VarSort_Type (lam. lam ty. checkBeforeUnify tv ty) () r.sort;
            r.sort
        in
        let updated = Unbound {{r with level = mini r.level tv.level}
                                  with sort  = sort} in
        modref t.contents updated
    else
      checkBeforeUnify tv (resolveLink ty)
end

lang FunTypeUnify = Unify + FunTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyArrow {from = from1, to = to1}, TyArrow {from = from2, to = to2}) ->
    unifyTypes env (from1, from2);
    unifyTypes env (to1, to2)
end

lang AppTypeUnify = Unify + AppTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyApp t1, TyApp t2) ->
    unifyTypes env (t1.lhs, t2.lhs);
    unifyTypes env (t1.rhs, t2.rhs)
end

lang AllTypeUnify = UnifyFields + AllTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyAll t1, TyAll t2) ->
    (match (t1.sort, t2.sort) with (RecordVar r1, RecordVar r2) then
       unifyFieldsStrict env r1.fields r2.fields
     else if eqi (constructorTag t1.sort) (constructorTag t2.sort) then ()
     else unificationError (_sort2str t1.ident t1.sort) (_sort2str t2.ident t2.sort));
    let env = {env with names = biInsert (t1.ident, t2.ident) env.names} in
    unifyTypes env (t1.ty, t2.ty)

  sem checkBeforeUnify (tv : FlexVarRec) =
  | TyAll t ->
    match tv.sort with WeakVar _ then
      let msg = join [
        "Type check failed: unification failure\n",
        "Attempted to unify monomorphic type variable with polymorphic type!\n"
      ] in
      infoErrorExit (deref errInfo) msg
    else
      sfold_VarSort_Type (lam. lam ty. checkBeforeUnify tv ty) () t.sort;
      checkBeforeUnify tv t.ty
end

lang ConTypeUnify = Unify + ConTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyCon t1 & ty1, TyCon t2 & ty2) ->
    if nameEq t1.ident t2.ident then ()
    else unificationError (_type2str ty1) (_type2str ty2)
end

lang BoolTypeUnify = Unify + BoolTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyBool _, TyBool _) -> ()
end

lang IntTypeUnify = Unify + IntTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyInt _, TyInt _) -> ()
end

lang FloatTypeUnify = Unify + FloatTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyFloat _, TyFloat _) -> ()
end

lang CharTypeUnify = Unify + CharTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyChar _, TyChar _) -> ()
end

lang UnknownTypeUnify = Unify + UnknownTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyUnknown _, _)
  | (_, TyUnknown _) ->
    ()
end

lang SeqTypeUnify = Unify + SeqTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TySeq t1, TySeq t2) ->
    unifyTypes env (t1.ty, t2.ty)
end

lang TensorTypeUnify = Unify + TensorTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyTensor t1, TyTensor t2) ->
    unifyTypes env (t1.ty, t2.ty)
end

lang RecordTypeUnify = UnifyFields + RecordTypeAst
  sem unifyBase (env : UnifyEnv) =
  | (TyRecord t1, TyRecord t2) ->
    unifyFieldsStrict env t1.fields t2.fields
end

------------------------------------
-- INSTANTIATION / GENERALIZATION --
------------------------------------

let newflexvar =
  lam sort. lam level. lam info.
  tyFlexUnbound info (nameSym "a") level sort

let newvarWeak = use VarSortAst in
  newflexvar (WeakVar ())
let newvar = use VarSortAst in
  newflexvar (TypeVar ())
let newrecvar = use VarSortAst in
  lam fields. newflexvar (RecordVar {fields = fields})

lang Generalize = AllTypeAst
  -- Instantiate the top-level type variables of `ty' with fresh schematic variables.
  sem inst (lvl : Level) =
  | ty ->
    match stripTyAll ty with (vars, ty) in
    if gti (length vars) 0 then
      let inserter = lam subst. lam v : (Name, VarSort).
        let sort = smap_VarSort_Type (instBase subst) v.1 in
        mapInsert v.0 (newflexvar sort lvl (infoTy ty)) subst
      in
      let subst = foldl inserter (mapEmpty nameCmp) vars in
      instBase subst ty
    else
      ty

  sem instBase (subst : Map Name Type) =
  | ty ->
    smap_Type_Type (instBase subst) ty

  -- Generalize all flexible (schematic) type variables in `ty'.
  sem gen (lvl : Level) =
  | ty ->
    match genBase lvl ty with (vars, genTy) in
    let fstEq = lam v1 : (Name, VarSort). lam v2 : (Name, VarSort). nameEq v1.0 v2.0 in
    let vars = distinct fstEq vars in
    let iteratee = lam v : (Name, VarSort). lam ty.
      let sort = match v.1 with WeakVar _ then TypeVar () else v.1 in
      TyAll {info = infoTy genTy, ident = v.0, ty = ty, sort = sort}
    in
    foldr iteratee genTy vars

  sem genBase (lvl : Level) =
  | ty ->
    smapAccumL_Type_Type (lam vars1. lam ty.
      match genBase lvl ty with (vars2, ty) in
      (concat vars1 vars2, ty)
    ) [] ty
end

lang VarTypeGeneralize = Generalize + VarTypeAst
  sem instBase (subst : Map Name Type) =
  | TyVar {ident = n} & ty ->
    match mapLookup n subst with Some tyvar then tyvar
    else ty
end

lang FlexTypeGeneralize = Generalize + FlexTypeAst + VarTypeAst
  sem genBase (lvl : Level) =
  | TyFlex t & ty ->
    match deref t.contents with Unbound {ident = n, level = k, sort = s} then
      if gti k lvl then
        -- Var is free, generalize
        let f = lam vars1. lam ty.
          match genBase lvl ty with (vars2, ty) in
          (concat vars1 vars2, ty)
        in
        match smapAccumL_VarSort_Type f [] s with (vars, sort) in
        (snoc vars (n, sort), TyVar {info = t.info, ident = n})
      else
        -- Var is bound in previous let, don't generalize
        ([], ty)
    else
      genBase lvl (resolveLink ty)
end

-- The default cases handle all other constructors!

-------------------
-- TYPE CHECKING --
-------------------

lang TypeCheck = Unify + Generalize
  -- Type check `tm', with FreezeML-style type inference.
  sem typeCheck =
  | tm ->
    typeCheckExpr _tcEnvEmpty tm

  -- Type check `expr' under the type environment `env'
  sem typeCheckExpr (env : TCEnv) =
  | tm ->
    modref errInfo (infoTm tm);
    typeCheckBase env tm

  sem typeCheckBase (env : TCEnv) =
  -- Intentionally left blank
end

lang PatTypeCheck = Unify
  sem typeCheckPat (env : TCEnv) =
  -- Intentionally left blank
end

lang VarTypeCheck = TypeCheck + VarAst
  sem typeCheckBase (env : TCEnv) =
  | TmVar t ->
    match mapLookup t.ident env.varEnv with Some ty then
      let ty =
        if t.frozen then ty
        else inst env.currentLvl ty
      in
      TmVar {t with ty = ty}
    else
      let msg = join [
        "Type check failed: reference to unbound variable: ",
        nameGetStr t.ident, "\n"
      ] in
      infoErrorExit t.info msg
end

lang LamTypeCheck = TypeCheck + LamAst
  sem typeCheckBase (env : TCEnv) =
  | TmLam t ->
    let tyX = optionGetOrElse
      -- No type annotation: assign a monomorphic type variable to x
      (lam. newvarWeak env.currentLvl t.info)
      -- Type annotation: assign x its annotated type
      (sremoveUnknown t.tyIdent)
    in
    let body = typeCheckExpr (_insertVar t.ident tyX env) t.body in
    let tyLam = ityarrow_ t.info tyX (tyTm body) in
    TmLam {{t with body = body}
              with ty = tyLam}
end

lang AppTypeCheck = TypeCheck + AppAst
  sem typeCheckBase (env : TCEnv) =
  | TmApp t ->
    let lhs = typeCheckExpr env t.lhs in
    let rhs = typeCheckExpr env t.rhs in
    let tyRes = newvar env.currentLvl t.info in
    unify env (tyTm lhs) (ityarrow_ (infoTm lhs) (tyTm rhs) tyRes);
    TmApp {{{t with lhs = lhs}
               with rhs = rhs}
               with ty = tyRes}
end

lang LetTypeCheck = TypeCheck + LetAst
  sem typeCheckBase (env : TCEnv) =
  | TmLet t ->
    let lvl = env.currentLvl in
    let body = typeCheckExpr {env with currentLvl = addi 1 lvl} t.body in
    let tyBody = optionMapOrElse
      -- No type annotation: generalize the inferred type
      (lam. gen lvl (tyTm body))
      -- Type annotation: unify the annotated type with the inferred one
      (lam ty.
        -- TODO(aathn, 2021-11-16): Simply stripping the annotated tyalls is
        -- insufficient if they happen to contains bounds. Then, we should
        -- instantiate the variables in the annotated type before unifying.
        -- For now such annotations are not supported though.
        match stripTyAll ty with (_, tyAnnot) in
        unify env tyAnnot (tyTm body);
        ty)
      (sremoveUnknown t.tyBody)
    in
    let inexpr = typeCheckExpr (_insertVar t.ident tyBody env) t.inexpr in
    TmLet {{{t with body = body}
               with inexpr = inexpr}
               with ty = tyTm inexpr}
end

lang RecLetsTypeCheck = TypeCheck + RecLetsAst
  sem typeCheckBase (env : TCEnv) =
  | TmRecLets t ->
    let lvl = env.currentLvl in

    -- First: Generate a new environment containing the recursive bindings
    let recLetEnvIteratee = lam acc. lam b : RecLetBinding.
      let tyBinding = optionGetOrElse
        (lam. newvar (addi 1 lvl) b.info)
        (sremoveUnknown b.tyBody)
      in
      _insertVar b.ident tyBinding acc
    in
    let recLetEnv : TCEnv = foldl recLetEnvIteratee env t.bindings in

    -- Second: Type check the body of each binding in the new environment
    let typeCheckBinding = lam b : RecLetBinding.
      let body = typeCheckExpr {recLetEnv with currentLvl = addi 1 lvl} b.body in
      optionMapOrElse
        -- No type annotation: unify the inferred type of the body with the
        -- inferred type of the binding
        (lam.
          match mapLookup b.ident recLetEnv.varEnv with Some ty in
          unify env ty (tyTm body))
        -- Type annotation: unify the inferred type of the body with the annotated one
        (lam ty.
          match stripTyAll ty with (_, tyAnnot) in
          unify env tyAnnot (tyTm body))
        (sremoveUnknown b.tyBody);
      {b with body = body}
    in
    let bindings = map typeCheckBinding t.bindings in

    -- Third: Produce a new environment with generalized types
    let envIteratee = lam acc. lam b : RecLetBinding.
      let tyBody = optionGetOrElse
        (lam. gen lvl (tyTm b.body))
        (sremoveUnknown b.tyBody)
      in
      _insertVar b.ident tyBody acc
    in
    let env = foldl envIteratee env bindings in
    let inexpr = typeCheckExpr env t.inexpr in
    TmRecLets {{{t with bindings = bindings}
                   with inexpr = inexpr}
                   with ty = tyTm inexpr}
end

lang MatchTypeCheck = TypeCheck + PatTypeCheck + MatchAst
  sem typeCheckBase (env : TCEnv) =
  | TmMatch t ->
    let target = typeCheckExpr env t.target in
    match typeCheckPat env t.pat with (thnEnv, pat) in
    unify env (tyTm target) (tyPat pat);
    let thn = typeCheckExpr thnEnv t.thn in
    let els = typeCheckExpr env t.els in
    unify env (tyTm thn) (tyTm els);
    TmMatch {{{{{t with target = target}
                   with thn = thn}
                   with els = els}
                   with ty = tyTm thn}
                   with pat = pat}
end

lang ConstTypeCheck = TypeCheck + MExprConstType
  sem typeCheckBase (env : TCEnv) =
  | TmConst t ->
    recursive let f = lam ty. smap_Type_Type f (tyWithInfo t.info ty) in
    let ty = inst env.currentLvl (f (tyConst t.val)) in
    TmConst {t with ty = ty}
end

lang SeqTypeCheck = TypeCheck + SeqAst
  sem typeCheckBase (env : TCEnv) =
  | TmSeq t ->
    let elemTy = newvar env.currentLvl t.info in
    let tms = map (typeCheckExpr env) t.tms in
    iter (compose (unify env elemTy) tyTm) tms;
    TmSeq {{t with tms = tms}
              with ty = ityseq_ t.info elemTy}
end

lang FlexSetLevel = FlexTypeAst
  sem setLevel (lvl : Int) =
  | TyFlex t & ty ->
    match deref t.contents with Unbound r then
      modref t.contents (Unbound {r with level = lvl});
      sfold_VarSort_Type (lam. lam ty. setLevel lvl ty) () r.sort
    else
      setLevel lvl (resolveLink ty)
  | ty ->
    sfold_Type_Type (lam. lam ty. setLevel lvl ty) () ty
end

lang RecordTypeCheck = TypeCheck + RecordAst + RecordTypeAst + FlexSetLevel
  sem typeCheckBase (env : TCEnv) =
  | TmRecord t ->
    let bindings = mapMap (typeCheckExpr env) t.bindings in
    let bindingTypes = mapMap tyTm bindings in
    let labels = mapKeys t.bindings in
    let ty = TyRecord {fields = bindingTypes, labels = labels, info = t.info} in
    TmRecord {{t with bindings = bindings}
                 with ty = ty}
  | TmRecordUpdate t ->
    let rec = typeCheckExpr env t.rec in
    let value = typeCheckExpr env t.value in
    let fields = mapInsert t.key (tyTm value) (mapEmpty cmpSID) in
    unify env (tyTm rec) (newrecvar fields env.currentLvl (infoTm rec));
    (if env.disableRecordPolymorphism then setLevel 0 (tyTm rec) else ());
    TmRecordUpdate {{{t with rec = rec}
                        with value = value}
                        with ty = tyTm rec}
end

lang TypeTypeCheck = TypeCheck + TypeAst
  sem typeCheckBase (env : TCEnv) =
  | TmType t ->
    let isAlias =
      match t.tyIdent with TyVariant {constrs = constrs} then
        not (mapIsEmpty constrs)
      else true
    in
    let env = if isAlias then _insertTyCon t.ident t.tyIdent env else env in
    let inexpr = typeCheckExpr env t.inexpr in
    TmType {{t with inexpr = inexpr}
               with ty = tyTm inexpr}
end

lang DataTypeCheck = TypeCheck + DataAst
  sem typeCheckBase (env : TCEnv) =
  | TmConDef t ->
    let inexpr = typeCheckExpr (_insertCon t.ident t.tyIdent env) t.inexpr in
    TmConDef {{t with inexpr = inexpr}
                 with ty = tyTm inexpr}
  | TmConApp t ->
    let body = typeCheckExpr env t.body in
    match mapLookup t.ident env.conEnv with Some lty then
      match inst env.currentLvl lty with TyArrow {from = from, to = to} in
      unify env (tyTm body) from;
      TmConApp {{t with body = body}
                   with ty   = to}
    else
      let msg = join [
        "Type check failed: reference to unbound constructor: ",
        nameGetStr t.ident, "\n"
      ] in
      infoErrorExit t.info msg
end

lang UtestTypeCheck = TypeCheck + UtestAst
  sem typeCheckBase (env : TCEnv) =
  | TmUtest t ->
    let test = typeCheckExpr env t.test in
    let expected = typeCheckExpr env t.expected in
    let next = typeCheckExpr env t.next in
    let tusing = optionMap (typeCheckExpr env) t.tusing in
    (match tusing with Some tu then
       unify env (tyTm tu) (tyarrows_ [tyTm test, tyTm expected, tybool_])
     else
       unify env (tyTm test) (tyTm expected));
    TmUtest {{{{{t with test = test}
                   with expected = expected}
                   with next = next}
                   with tusing = tusing}
                   with ty = tyTm next}
end

lang NeverTypeCheck = TypeCheck + NeverAst
  sem typeCheckBase (env : TCEnv) =
  | TmNever t -> TmNever {t with ty = newvar env.currentLvl t.info}
end

lang ExtTypeCheck = TypeCheck + ExtAst
  sem typeCheckBase (env : TCEnv) =
  | TmExt t ->
    let env = {env with varEnv = mapInsert t.ident t.tyIdent env.varEnv} in
    let inexpr = typeCheckExpr env t.inexpr in
    TmExt {{t with inexpr = inexpr}
              with ty = tyTm inexpr}
end

---------------------------
-- PATTERN TYPE CHECKING --
---------------------------

lang NamedPatTypeCheck = PatTypeCheck + NamedPat
  sem typeCheckPat (env : TCEnv) =
  | PatNamed t ->
    let patTy = newvar env.currentLvl t.info in
    let env =
      match t.ident with PName n then
        _insertVar n patTy env
      else env
    in
    (env, PatNamed {t with ty = patTy})
end

lang SeqTotPatTypeCheck = PatTypeCheck + SeqTotPat
  sem typeCheckPat (env : TCEnv) =
  | PatSeqTot t ->
    let elemTy = newvar env.currentLvl t.info in
    match mapAccumL typeCheckPat env t.pats with (env, pats) in
    iter (compose (unify env elemTy) tyPat) pats;
    (env, PatSeqTot {{t with pats = pats}
                        with ty = ityseq_ t.info elemTy})
end

lang SeqEdgePatTypeCheck = PatTypeCheck + SeqEdgePat
  sem typeCheckPat (env : TCEnv) =
  | PatSeqEdge t ->
    let elemTy = newvar env.currentLvl t.info in
    let seqTy = ityseq_ t.info elemTy in
    let unifyPat = compose (unify env elemTy) tyPat in
    match mapAccumL typeCheckPat env t.prefix with (env, prefix) in
    iter unifyPat prefix;
    match mapAccumL typeCheckPat env t.postfix with (env, postfix) in
    iter unifyPat postfix;
    let env =
      match t.middle with PName n then _insertVar n seqTy env
      else env
    in
    (env, PatSeqEdge {{{t with prefix = prefix}
                          with postfix = postfix}
                          with ty = seqTy})
end

lang RecordPatTypeCheck = PatTypeCheck + RecordPat + FlexSetLevel
  sem typeCheckPat (env : TCEnv) =
  | PatRecord t ->
    let typeCheckBinding = lam env. lam. lam pat. typeCheckPat env pat in
    match mapMapAccum typeCheckBinding env t.bindings with (env, bindings) in
    let env : TCEnv = env in
    let ty = newrecvar (mapMap tyPat bindings) env.currentLvl t.info in
    (if env.disableRecordPolymorphism then setLevel 0 ty else ());
    (env, PatRecord {{t with bindings = bindings}
                        with ty = ty})
end

lang DataPatTypeCheck = TypeCheck + DataPat
  sem typeCheckPat (env : TCEnv) =
  | PatCon t ->
    match mapLookup t.ident env.conEnv with Some ty then
      match inst env.currentLvl ty with TyArrow {from = from, to = to} in
      match typeCheckPat env t.subpat with (env, subpat) in
      unify env (tyPat subpat) from;
      (env, PatCon {{t with subpat = subpat}
                       with ty = to})
    else
      let msg = join [
        "Type check failed: reference to unbound constructor: ",
        nameGetStr t.ident, "\n"
      ] in
      infoErrorExit t.info msg
end

lang IntPatTypeCheck = PatTypeCheck + IntPat
  sem typeCheckPat (env : TCEnv) =
  | PatInt t -> (env, PatInt {t with ty = TyInt {info = t.info}})
end

lang CharPatTypeCheck = PatTypeCheck + CharPat
  sem typeCheckPat (env : TCEnv) =
  | PatChar t -> (env, PatChar {t with ty = TyChar {info = t.info}})
end

lang BoolPatTypeCheck = PatTypeCheck + BoolPat
  sem typeCheckPat (env : TCEnv) =
  | PatBool t -> (env, PatBool {t with ty = TyBool {info = t.info}})
end

lang AndPatTypeCheck = PatTypeCheck + AndPat
  sem typeCheckPat (env : TCEnv) =
  | PatAnd t ->
    match typeCheckPat env t.lpat with (env, lpat) in
    match typeCheckPat env t.rpat with (env, rpat) in
    unify env (tyPat lpat) (tyPat rpat);
    (env, PatAnd {{{t with lpat = lpat} with rpat = rpat} with ty = tyPat lpat})
end

-- TODO(aathn, 2021-11-11): This definition is incorrect as it does not check
-- that variables from different branches have the same type
lang OrPatTypeCheck = PatTypeCheck + OrPat
  sem typeCheckPat (env : TCEnv) =
  | PatOr t ->
    match typeCheckPat env t.lpat with (env, lpat) in
    match typeCheckPat env t.rpat with (env, rpat) in
    unify env (tyPat lpat) (tyPat rpat);
    (env, PatOr {{{t with lpat = lpat} with rpat = rpat} with ty = tyPat lpat})
end

lang NotPatTypeCheck = PatTypeCheck + NotPat
  sem typeCheckPat (env : TCEnv) =
  | PatNot t ->
    match typeCheckPat env t.subpat with (env, subpat) in
    (env, PatNot {{t with subpat = subpat} with ty = tyPat subpat})
end


lang MExprTypeCheck =

  -- Type unification
  VarTypeUnify + FlexTypeUnify + FunTypeUnify + AppTypeUnify + AllTypeUnify +
  ConTypeUnify + SeqTypeUnify + BoolTypeUnify + IntTypeUnify + FloatTypeUnify +
  CharTypeUnify + UnknownTypeUnify + TensorTypeUnify + RecordTypeUnify +

  -- Type generalization
  VarTypeGeneralize + FlexTypeGeneralize +

  -- Terms
  VarTypeCheck + LamTypeCheck + AppTypeCheck + LetTypeCheck + RecLetsTypeCheck +
  MatchTypeCheck + ConstTypeCheck + SeqTypeCheck + RecordTypeCheck +
  TypeTypeCheck + DataTypeCheck + UtestTypeCheck + NeverTypeCheck + ExtTypeCheck +

  -- Patterns
  NamedPatTypeCheck + SeqTotPatTypeCheck + SeqEdgePatTypeCheck +
  RecordPatTypeCheck + DataPatTypeCheck + IntPatTypeCheck + CharPatTypeCheck +
  BoolPatTypeCheck + AndPatTypeCheck + OrPatTypeCheck + NotPatTypeCheck

end

lang TestLang = MExprTypeCheck + MExprEq end

mexpr

use TestLang in

let gen_  = lam tm. bind_ (ulet_ "x" tm) (freeze_ (var_ "x")) in
let inst_ = lam tm. bind_ (ulet_ "x" tm) (var_ "x") in

let a = tyvar_ "a" in
let b = tyvar_ "b" in
let fa = newvar 0 (NoInfo ()) in
let fb = newvar 0 (NoInfo ()) in
let wa = newvarWeak 0 (NoInfo ()) in
let wb = newvarWeak 0 (NoInfo ()) in

let tychoose_ = tyall_ "a" (tyarrows_ [a, a, a]) in
let choose_ = ("choose", tychoose_) in

let idbody_ = ulam_ "y" (var_ "y") in
let tyid_ = tyall_ "a" (tyarrow_ a a) in
let id_ = ("id", tyid_) in

let idsbody_ = bind_ id_ (seq_ [freeze_ (var_ "id")]) in
let tyids_ = tyseq_ tyid_ in
let ids_ = ("ids", tyids_) in

let autobody_ = lam_ "x" tyid_ (app_ (var_ "x") (freeze_ (var_ "x"))) in
let tyauto_ = tyarrow_ tyid_ tyid_ in
let auto_ = ("auto", tyauto_) in

let auto1body_ = lam_ "x" tyid_ (app_ (var_ "x") (var_ "x")) in
let tyauto1_ = tyall_ "b" (tyarrows_ [tyid_, b, b]) in
let auto1_ = ("auto1", tyauto1_) in

let polybody_ = lam_ "f" tyid_ (utuple_ [app_ (var_ "f") (int_ 1), app_ (var_ "f") true_]) in
let typoly_ = tyarrow_ tyid_ (tytuple_ [tyint_, tybool_]) in
let poly_ = ("poly", typoly_) in

type TypeTest = {
  -- Name of the test case, for documentation purposes
  name : String,
  -- The term to typecheck
  tm : Expr,
  -- Its expected type
  ty : Type,
  -- Environment assigning types to functions like id, choose, et.c.
  env : [(String, Type)]
}
in

let typeOf = lam test : TypeTest.
  let env = foldr (lam n : (String, Type).
    mapInsert (nameNoSym n.0) n.1) (mapEmpty nameCmp) test.env in
  tyTm (typeCheckExpr {_tcEnvEmpty with varEnv = env} test.tm)
in

let runTest =
  lam test : TypeTest.
  -- Make sure to print the test name if the test fails.
  let eqTypeTest = lam a : Type. lam b : Type.
    if eqType a b then true
    else print (join ["\n ** Type test FAILED: ", test.name, " **"]); false
  in
  utest typeOf test with test.ty using eqTypeTest in ()
in

let tests = [

  -- Examples from the paper
  -- A : Polymorphic Instantiation
  {name = "A1",
   tm = ulam_ "x" idbody_,
   ty = tyarrows_ [wa, wb, wb],
   env = []},

  {name = "A1o",
   tm = gen_ (ulam_ "x" idbody_),
   ty = tyalls_ ["a", "b"] (tyarrows_ [a, b, b]),
   env = []},

  {name = "A2",
   tm = app_ (var_ "choose") (var_ "id"),
   ty = tyarrows_ [tyarrow_ fa fa, fa, fa],
   env = [choose_, id_]},

  {name = "A2o",
   tm = app_ (var_ "choose") (freeze_ (var_ "id")),
   ty = tyauto_,
   env = [choose_, id_]},

  {name = "A3",
   tm = appf2_ (var_ "choose") empty_ (var_ "ids"),
   ty = tyids_,
   env = [choose_, ids_]},

  {name = "A4",
   tm = auto1body_,
   ty = tyarrows_ [tyid_, fb, fb],
   env = []},

  {name = "A4o",
   tm = autobody_,
   ty = tyauto_,
   env = []},

  {name = "A5",
   tm = app_ (var_ "id") (var_ "auto"),
   ty = tyauto_,
   env = [id_, auto_]},

  {name = "A6",
   tm = app_ (var_ "id") (var_ "auto1"),
   ty = tyarrows_ [tyid_, fb, fb],
   env = [id_, auto1_]},

  {name = "A6o",
   tm = app_ (var_ "id") (freeze_ (var_ "auto1")),
   ty = tyauto1_,
   env = [id_, auto1_]},

  {name = "A7",
   tm = appf2_ (var_ "choose") (var_ "id") (var_ "auto"),
   ty = tyauto_,
   env = [choose_, id_, auto_]},

  -- We can't handle negative tests yet, since the type checker errors on failure
  -- {name = "A8",
  --  tm = appf2_ (var_ "choose") (var_ "id") (var_ "auto1"),
  --  ty = fails,
  --  env = [choose_, id_, auto1_]}

  {name = "A9*",
   tm = appf2_ (var_ "f") (app_ (var_ "choose") (freeze_ (var_ "id"))) (var_ "ids"),
   ty = tyid_,
   env = [
     choose_,
     id_,
     ids_,
     ("f", tyall_ "a" (tyarrows_ [tyarrow_ a a, tyseq_ a, a]))
   ]},

  {name = "A10*",
   tm = app_ (var_ "poly") (freeze_ (var_ "id")),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_, id_]},

  {name = "A11*",
   tm = app_ (var_ "poly") (gen_ idbody_),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_]},

  {name = "A12*",
   tm = appf2_ (var_ "id") (var_ "poly") (gen_ idbody_),
   ty = tytuple_ [tyint_, tybool_],
   env = [poly_, id_]},

  -- TODO(aathn, 2021-10-02): Add remaining tests from the paper
  -- B : Inference with Polymorphic Arguments
  -- C : Functions on Polymorphic Lists
  -- D : Application Functions
  -- E : Eta-Expansion
  -- F : FreezeML Programs

  -- Other tests
  {name = "RecLets1",
   tm = bindall_ [
     ureclets_ [
       ("x", ulam_ "n" (app_ (var_ "y") false_)),
       ("y", ulam_ "n" (app_ (var_ "x") false_))
     ],
     var_ "x"
   ],
   ty = tyarrow_ tybool_ fa,
   env = []},

  {name = "RecLets2",
   tm = bindall_ [
     ureclets_ [
       ("even", ulam_ "n"
         (if_ (eqi_ (var_ "n") (int_ 0))
           true_
           (app_ (var_ "odd") (subi_ (var_ "n") (int_ 1))))),
       ("odd", ulam_ "n"
         (if_ (eqi_ (var_ "n") (int_ 0))
           false_
           (app_ (var_ "even") (subi_ (var_ "n") (int_ 1)))))
     ],
     var_ "even"
   ],
   ty = tyarrow_ tyint_ tybool_,
   env = []},

  {name = "Match1",
   tm = if_ true_ (int_ 1) (int_ 0),
   ty = tyint_,
   env = []},

  {name = "Match2",
   tm = ulam_ "x"
     (match_ (var_ "x") (pvar_ "y") (addi_ (var_ "y") (int_ 1)) (int_ 0)),
   ty = tyarrow_ tyint_ tyint_,
   env = []},

  {name = "Match3",
   tm = match_
     (seq_ [str_ "a", str_ "b", str_ "c", str_ "d"])
     (pseqedge_ [pseqtot_ [pchar_ 'a']] "mid" [pseqtot_ [pchar_ 'd']])
     (var_ "mid")
     never_,
   ty = tyseq_ tystr_,
   env = []},

  {name = "Const1",
   tm = addi_ (int_ 5) (int_ 2),
   ty = tyint_,
   env = []},

  {name = "Const2",
   tm = cons_ (int_ 0) empty_,
   ty = tyseq_ tyint_,
   env = []},

  {name = "Const3",
   tm = ulam_ "x" (int_ 0),
   ty = tyarrow_ wa tyint_,
   env = []},

  {name = "Seq1",
   tm = seq_ [],
   ty = tyseq_ fa,
   env = []},

  {name = "Seq2",
   tm = seq_ [int_ 1, int_ 2],
   ty = tyseq_ tyint_,
   env = []},

  {name = "Seq3",
   tm = seq_ [seq_ [int_ 1, int_ 2],
              seq_ [int_ 3, int_ 4]],
   ty = tyseq_ (tyseq_ tyint_),
   env = []},

  {name = "Record1",
   tm = uunit_,
   ty = tyunit_,
   env = []},

  {name = "Record2",
   tm = utuple_ [int_ 0, true_],
   ty = tytuple_ [tyint_, tybool_],
   env = []},

  {name = "Record3",
   tm = urecord_ [
     ("a", int_ 0), ("b", float_ 2.718), ("c", urecord_ []),
     ("d", urecord_ [
       ("e", seq_ [int_ 1, int_ 2]),
       ("f", urecord_ [
         ("x", var_ "x"), ("y", var_ "y"), ("z", var_ "z")
       ])
     ])
   ],
   ty = tyrecord_ [
     ("a", tyint_), ("b", tyfloat_), ("c", tyunit_),
     ("d", tyrecord_ [
       ("e", tyseq_ tyint_),
       ("f", tyrecord_ [
         ("x", tyint_), ("y", tyfloat_), ("z", tybool_)
       ])
     ])
   ],
   env = [("x", tyint_), ("y", tyfloat_), ("z", tybool_)]},

  {name = "Record4",
   tm = recordupdate_ (urecord_ [
     ("a", int_ 0),
     ("b", float_ 2.718)
   ]) "a" (int_ 1),
   ty = tyrecord_ [
     ("a", tyint_),
     ("b", tyfloat_)
   ],
   env = []},

  {name = "Record5",
   tm = bind_
     (ulet_ "f"
       (ulam_ "r" (ulam_ "x" (ulam_ "y"
         (recordupdate_
           (recordupdate_
             (var_ "r") "x" (var_ "x"))
           "y" (var_ "y"))))))
     (freeze_ (var_ "f")),
   ty =
     let fields =  mapInsert (stringToSid "x") wa
                  (mapInsert (stringToSid "y") wb
                  (mapEmpty cmpSID))
     in
     let r = newrecvar fields 0 (NoInfo ()) in
     tyarrows_ [r, wa, wb, r],
   env = []},

  {name = "Con1",
   tm = bindall_ [
     type_ "Tree" (tyvariant_ []),
     condef_ "Branch" (tyarrow_ (tytuple_ [tycon_ "Tree", tycon_ "Tree"])
                                (tycon_ "Tree")),
     condef_ "Leaf" (tyarrow_ (tyseq_ tyint_) (tycon_ "Tree")),
     ulet_ "t" (conapp_ "Branch" (utuple_ [
       conapp_ "Leaf" (seq_ [int_ 1, int_ 2, int_ 3]),
       conapp_ "Branch" (utuple_ [
         conapp_ "Leaf" (seq_ [int_ 2]),
         conapp_ "Leaf" (seq_ [])])])),
     (match_ (var_ "t")
       (pcon_ "Branch" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]))
       (match_ (var_ "lhs")
         (pcon_ "Leaf" (pvar_ "n"))
         (var_ "n")
         never_)
       never_)
   ],
   ty = tyseq_ tyint_,
   env = []},

  {name = "Type1",
   tm = bindall_ [
     type_ "Foo" (tyrecord_ [("x", tyint_)]),
     ulet_ "f" (lam_ "r" (tycon_ "Foo") (recordupdate_ (var_ "r") "x" (int_ 1))),
     app_ (var_ "f") (urecord_ [("x", int_ 0)])
   ],
   ty = tyrecord_ [("x", tyint_)],
   env = []},

  {name = "Utest1",
   tm = utest_ (int_ 1) (addi_ (int_ 0) (int_ 1)) false_,
   ty = tybool_,
   env = []},

  {name = "Utest2",
   tm = utestu_ (int_ 1) true_ false_ (ulam_ "x" idbody_),
   ty = tybool_,
   env = []},

  {name = "Never1",
   tm = never_,
   ty = fa,
   env = []}

]
in

iter runTest tests;

()

-- TODO(aathn, 2021-09-28): Proper error reporting and propagation
-- Report a "stack trace" when encountering a unification failure

-- TODO(aathn, 2021-09-28): Value restriction

