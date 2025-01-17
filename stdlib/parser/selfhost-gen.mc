include "seq.mc"

include "parser/ll1.mc"

include "parser/breakable.mc"

lang SelfhostBaseAst

  syn File =
  syn Decl =
  syn Regex =
  syn Expr =

  sem smapAccumL_File_File : all a. ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_File f acc =
  | x ->
    (acc, x)

  sem smap_File_File : ((File) -> (File)) -> ((File) -> (File))
  sem smap_File_File f =
  | x ->
    (smapAccumL_File_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_File : all a. ((a) -> ((File) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_File f acc =
  | x ->
    (smapAccumL_File_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_File_Decl : all a. ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_Decl f acc =
  | x ->
    (acc, x)

  sem smap_File_Decl : ((Decl) -> (Decl)) -> ((File) -> (File))
  sem smap_File_Decl f =
  | x ->
    (smapAccumL_File_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_Decl : all a. ((a) -> ((Decl) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_Decl f acc =
  | x ->
    (smapAccumL_File_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_File_Regex : all a. ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_Regex f acc =
  | x ->
    (acc, x)

  sem smap_File_Regex : ((Regex) -> (Regex)) -> ((File) -> (File))
  sem smap_File_Regex f =
  | x ->
    (smapAccumL_File_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_Regex : all a. ((a) -> ((Regex) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_Regex f acc =
  | x ->
    (smapAccumL_File_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_File_Expr : all a. ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_Expr f acc =
  | x ->
    (acc, x)

  sem smap_File_Expr : ((Expr) -> (Expr)) -> ((File) -> (File))
  sem smap_File_Expr f =
  | x ->
    (smapAccumL_File_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_Expr : all a. ((a) -> ((Expr) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_Expr f acc =
  | x ->
    (smapAccumL_File_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_File : all a. ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_File f acc =
  | x ->
    (acc, x)

  sem smap_Decl_File : ((File) -> (File)) -> ((Decl) -> (Decl))
  sem smap_Decl_File f =
  | x ->
    (smapAccumL_Decl_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_File : all a. ((a) -> ((File) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_File f acc =
  | x ->
    (smapAccumL_Decl_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_Decl : all a. ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_Decl f acc =
  | x ->
    (acc, x)

  sem smap_Decl_Decl : ((Decl) -> (Decl)) -> ((Decl) -> (Decl))
  sem smap_Decl_Decl f =
  | x ->
    (smapAccumL_Decl_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_Decl : all a. ((a) -> ((Decl) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_Decl f acc =
  | x ->
    (smapAccumL_Decl_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_Regex : all a. ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_Regex f acc =
  | x ->
    (acc, x)

  sem smap_Decl_Regex : ((Regex) -> (Regex)) -> ((Decl) -> (Decl))
  sem smap_Decl_Regex f =
  | x ->
    (smapAccumL_Decl_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_Regex : all a. ((a) -> ((Regex) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_Regex f acc =
  | x ->
    (smapAccumL_Decl_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_Expr : all a. ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_Expr f acc =
  | x ->
    (acc, x)

  sem smap_Decl_Expr : ((Expr) -> (Expr)) -> ((Decl) -> (Decl))
  sem smap_Decl_Expr f =
  | x ->
    (smapAccumL_Decl_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_Expr : all a. ((a) -> ((Expr) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_Expr f acc =
  | x ->
    (smapAccumL_Decl_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_File : all a. ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_File f acc =
  | x ->
    (acc, x)

  sem smap_Regex_File : ((File) -> (File)) -> ((Regex) -> (Regex))
  sem smap_Regex_File f =
  | x ->
    (smapAccumL_Regex_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_File : all a. ((a) -> ((File) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_File f acc =
  | x ->
    (smapAccumL_Regex_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_Decl : all a. ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_Decl f acc =
  | x ->
    (acc, x)

  sem smap_Regex_Decl : ((Decl) -> (Decl)) -> ((Regex) -> (Regex))
  sem smap_Regex_Decl f =
  | x ->
    (smapAccumL_Regex_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_Decl : all a. ((a) -> ((Decl) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_Decl f acc =
  | x ->
    (smapAccumL_Regex_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_Regex : all a. ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_Regex f acc =
  | x ->
    (acc, x)

  sem smap_Regex_Regex : ((Regex) -> (Regex)) -> ((Regex) -> (Regex))
  sem smap_Regex_Regex f =
  | x ->
    (smapAccumL_Regex_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_Regex : all a. ((a) -> ((Regex) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_Regex f acc =
  | x ->
    (smapAccumL_Regex_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_Expr : all a. ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_Expr f acc =
  | x ->
    (acc, x)

  sem smap_Regex_Expr : ((Expr) -> (Expr)) -> ((Regex) -> (Regex))
  sem smap_Regex_Expr f =
  | x ->
    (smapAccumL_Regex_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_Expr : all a. ((a) -> ((Expr) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_Expr f acc =
  | x ->
    (smapAccumL_Regex_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_File : all a. ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_File f acc =
  | x ->
    (acc, x)

  sem smap_Expr_File : ((File) -> (File)) -> ((Expr) -> (Expr))
  sem smap_Expr_File f =
  | x ->
    (smapAccumL_Expr_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_File : all a. ((a) -> ((File) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_File f acc =
  | x ->
    (smapAccumL_Expr_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_Decl : all a. ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_Decl f acc =
  | x ->
    (acc, x)

  sem smap_Expr_Decl : ((Decl) -> (Decl)) -> ((Expr) -> (Expr))
  sem smap_Expr_Decl f =
  | x ->
    (smapAccumL_Expr_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Decl : all a. ((a) -> ((Decl) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_Decl f acc =
  | x ->
    (smapAccumL_Expr_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_Regex : all a. ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_Regex f acc =
  | x ->
    (acc, x)

  sem smap_Expr_Regex : ((Regex) -> (Regex)) -> ((Expr) -> (Expr))
  sem smap_Expr_Regex f =
  | x ->
    (smapAccumL_Expr_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Regex : all a. ((a) -> ((Regex) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_Regex f acc =
  | x ->
    (smapAccumL_Expr_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_Expr : all a. ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_Expr f acc =
  | x ->
    (acc, x)

  sem smap_Expr_Expr : ((Expr) -> (Expr)) -> ((Expr) -> (Expr))
  sem smap_Expr_Expr f =
  | x ->
    (smapAccumL_Expr_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Expr : all a. ((a) -> ((Expr) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_Expr f acc =
  | x ->
    (smapAccumL_Expr_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem get_File_info : (File) -> (Info)

  sem set_File_info : (Info) -> ((File) -> (File))

  sem mapAccum_File_info : all a. ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((File) -> ((a, File))))
  sem mapAccum_File_info f acc =
  | target ->
    match
      f
        acc
        (get_File_info
           target)
    with
      (acc, val)
    then
      (acc, set_File_info
        val
        target)
    else
      never

  sem map_File_info : ((Info) -> (Info)) -> ((File) -> (File))
  sem map_File_info f =
  | target ->
    set_File_info
      (f
         (get_File_info
            target))
      target

  sem get_Decl_info : (Decl) -> (Info)

  sem set_Decl_info : (Info) -> ((Decl) -> (Decl))

  sem mapAccum_Decl_info : all a. ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem mapAccum_Decl_info f acc =
  | target ->
    match
      f
        acc
        (get_Decl_info
           target)
    with
      (acc, val)
    then
      (acc, set_Decl_info
        val
        target)
    else
      never

  sem map_Decl_info : ((Info) -> (Info)) -> ((Decl) -> (Decl))
  sem map_Decl_info f =
  | target ->
    set_Decl_info
      (f
         (get_Decl_info
            target))
      target

  sem get_Regex_info : (Regex) -> (Info)

  sem set_Regex_info : (Info) -> ((Regex) -> (Regex))

  sem mapAccum_Regex_info : all a. ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem mapAccum_Regex_info f acc =
  | target ->
    match
      f
        acc
        (get_Regex_info
           target)
    with
      (acc, val)
    then
      (acc, set_Regex_info
        val
        target)
    else
      never

  sem map_Regex_info : ((Info) -> (Info)) -> ((Regex) -> (Regex))
  sem map_Regex_info f =
  | target ->
    set_Regex_info
      (f
         (get_Regex_info
            target))
      target

  sem get_Expr_info : (Expr) -> (Info)

  sem set_Expr_info : (Info) -> ((Expr) -> (Expr))

  sem mapAccum_Expr_info : all a. ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem mapAccum_Expr_info f acc =
  | target ->
    match
      f
        acc
        (get_Expr_info
           target)
    with
      (acc, val)
    then
      (acc, set_Expr_info
        val
        target)
    else
      never

  sem map_Expr_info : ((Info) -> (Info)) -> ((Expr) -> (Expr))
  sem map_Expr_info f =
  | target ->
    set_Expr_info
      (f
         (get_Expr_info
            target))
      target

end

lang FileAst = SelfhostBaseAst
  type FileRecord = {info: Info, name: {i: Info, v: String}, decls: [Decl]}

  syn File =
  | File FileRecord

  sem smapAccumL_File_Decl f acc =
  | File x ->
    match
      match
        let decls =
          x.decls
        in
        mapAccumL
          (lam acc1.
             lam x1: Decl.
               f
                 acc1
                 x1)
          acc
          decls
      with
        (acc, decls)
      then
        (acc, { x
          with
          decls =
            decls })
      else
        never
    with
      (acc, x)
    then
      (acc, File
        x)
    else
      never

  sem get_File_info =
  | File target ->
    target.info

  sem set_File_info val =
  | File target ->
    File
      { target
        with
        info =
          val }

end

lang StartDeclAst = SelfhostBaseAst
  type StartDeclRecord = {info: Info, name: {i: Info, v: Name}}

  syn Decl =
  | StartDecl StartDeclRecord

  sem get_Decl_info =
  | StartDecl target ->
    target.info

  sem set_Decl_info val =
  | StartDecl target ->
    StartDecl
      { target
        with
        info =
          val }

end

lang IncludeDeclAst = SelfhostBaseAst
  type IncludeDeclRecord = {info: Info, path: {i: Info, v: String}}

  syn Decl =
  | IncludeDecl IncludeDeclRecord

  sem get_Decl_info =
  | IncludeDecl target ->
    target.info

  sem set_Decl_info val =
  | IncludeDecl target ->
    IncludeDecl
      { target
        with
        info =
          val }

end

lang TypeDeclAst = SelfhostBaseAst
  type TypeDeclRecord = {info: Info, name: {i: Info, v: Name}, properties: [{val: Expr, name: {i: Info, v: String}}]}

  syn Decl =
  | TypeDecl TypeDeclRecord

  sem smapAccumL_Decl_Expr f acc =
  | TypeDecl x ->
    match
      match
        let properties =
          x.properties
        in
        mapAccumL
          (lam acc1.
             lam x1: {val: Expr, name: {i: Info, v: String}}.
               match
                 let val =
                   x1.val
                 in
                 f
                   acc1
                   val
               with
                 (acc1, val)
               then
                 (acc1, { x1
                   with
                   val =
                     val })
               else
                 never)
          acc
          properties
      with
        (acc, properties)
      then
        (acc, { x
          with
          properties =
            properties })
      else
        never
    with
      (acc, x)
    then
      (acc, TypeDecl
        x)
    else
      never

  sem get_Decl_info =
  | TypeDecl target ->
    target.info

  sem set_Decl_info val =
  | TypeDecl target ->
    TypeDecl
      { target
        with
        info =
          val }

end

lang TokenDeclAst = SelfhostBaseAst
  type TokenDeclRecord = {info: Info, name: (Option) ({i: Info, v: Name}), properties: [{val: Expr, name: {i: Info, v: String}}]}

  syn Decl =
  | TokenDecl TokenDeclRecord

  sem smapAccumL_Decl_Expr f acc =
  | TokenDecl x ->
    match
      match
        let properties =
          x.properties
        in
        mapAccumL
          (lam acc1.
             lam x1: {val: Expr, name: {i: Info, v: String}}.
               match
                 let val =
                   x1.val
                 in
                 f
                   acc1
                   val
               with
                 (acc1, val)
               then
                 (acc1, { x1
                   with
                   val =
                     val })
               else
                 never)
          acc
          properties
      with
        (acc, properties)
      then
        (acc, { x
          with
          properties =
            properties })
      else
        never
    with
      (acc, x)
    then
      (acc, TokenDecl
        x)
    else
      never

  sem get_Decl_info =
  | TokenDecl target ->
    target.info

  sem set_Decl_info val =
  | TokenDecl target ->
    TokenDecl
      { target
        with
        info =
          val }

end

lang PrecedenceTableDeclAst = SelfhostBaseAst
  type PrecedenceTableDeclRecord = {info: Info, levels: [{noeq: (Option) (Info), operators: [{i: Info, v: Name}]}], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]}

  syn Decl =
  | PrecedenceTableDecl PrecedenceTableDeclRecord

  sem get_Decl_info =
  | PrecedenceTableDecl target ->
    target.info

  sem set_Decl_info val =
  | PrecedenceTableDecl target ->
    PrecedenceTableDecl
      { target
        with
        info =
          val }

end

lang ProductionDeclAst = SelfhostBaseAst
  type ProductionDeclRecord = {nt: {i: Info, v: Name}, info: Info, kinf: (Option) (Info), name: {i: Info, v: Name}, assoc: (Option) ({i: Info, v: String}), kpref: (Option) (Info), kprod: (Option) (Info), regex: Regex, kpostf: (Option) (Info)}

  syn Decl =
  | ProductionDecl ProductionDeclRecord

  sem smapAccumL_Decl_Regex f acc =
  | ProductionDecl x ->
    match
      match
        let regex =
          x.regex
        in
        f
          acc
          regex
      with
        (acc, regex)
      then
        (acc, { x
          with
          regex =
            regex })
      else
        never
    with
      (acc, x)
    then
      (acc, ProductionDecl
        x)
    else
      never

  sem get_Decl_info =
  | ProductionDecl target ->
    target.info

  sem set_Decl_info val =
  | ProductionDecl target ->
    ProductionDecl
      { target
        with
        info =
          val }

end

lang RecordRegexAst = SelfhostBaseAst
  type RecordRegexRecord = {info: Info, regex: Regex}

  syn Regex =
  | RecordRegex RecordRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RecordRegex x ->
    match
      match
        let regex =
          x.regex
        in
        f
          acc
          regex
      with
        (acc, regex)
      then
        (acc, { x
          with
          regex =
            regex })
      else
        never
    with
      (acc, x)
    then
      (acc, RecordRegex
        x)
    else
      never

  sem get_Regex_info =
  | RecordRegex target ->
    target.info

  sem set_Regex_info val =
  | RecordRegex target ->
    RecordRegex
      { target
        with
        info =
          val }

end

lang EmptyRegexAst = SelfhostBaseAst
  type EmptyRegexRecord = {info: Info}

  syn Regex =
  | EmptyRegex EmptyRegexRecord

  sem get_Regex_info =
  | EmptyRegex target ->
    target.info

  sem set_Regex_info val =
  | EmptyRegex target ->
    EmptyRegex
      { target
        with
        info =
          val }

end

lang LiteralRegexAst = SelfhostBaseAst
  type LiteralRegexRecord = {val: {i: Info, v: String}, info: Info}

  syn Regex =
  | LiteralRegex LiteralRegexRecord

  sem get_Regex_info =
  | LiteralRegex target ->
    target.info

  sem set_Regex_info val =
  | LiteralRegex target ->
    LiteralRegex
      { target
        with
        info =
          val }

end

lang TokenRegexAst = SelfhostBaseAst
  type TokenRegexRecord = {arg: (Option) (Expr), info: Info, name: {i: Info, v: Name}}

  syn Regex =
  | TokenRegex TokenRegexRecord

  sem smapAccumL_Regex_Expr f acc =
  | TokenRegex x ->
    match
      match
        let arg =
          x.arg
        in
        optionMapAccum
          (lam acc1.
             lam x1.
               f
                 acc1
                 x1)
          acc
          arg
      with
        (acc, arg)
      then
        (acc, { x
          with
          arg =
            arg })
      else
        never
    with
      (acc, x)
    then
      (acc, TokenRegex
        x)
    else
      never

  sem get_Regex_info =
  | TokenRegex target ->
    target.info

  sem set_Regex_info val =
  | TokenRegex target ->
    TokenRegex
      { target
        with
        info =
          val }

end

lang RepeatPlusRegexAst = SelfhostBaseAst
  type RepeatPlusRegexRecord = {info: Info, left: Regex}

  syn Regex =
  | RepeatPlusRegex RepeatPlusRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RepeatPlusRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        (acc, { x
          with
          left =
            left })
      else
        never
    with
      (acc, x)
    then
      (acc, RepeatPlusRegex
        x)
    else
      never

  sem get_Regex_info =
  | RepeatPlusRegex target ->
    target.info

  sem set_Regex_info val =
  | RepeatPlusRegex target ->
    RepeatPlusRegex
      { target
        with
        info =
          val }

end

lang RepeatStarRegexAst = SelfhostBaseAst
  type RepeatStarRegexRecord = {info: Info, left: Regex}

  syn Regex =
  | RepeatStarRegex RepeatStarRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RepeatStarRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        (acc, { x
          with
          left =
            left })
      else
        never
    with
      (acc, x)
    then
      (acc, RepeatStarRegex
        x)
    else
      never

  sem get_Regex_info =
  | RepeatStarRegex target ->
    target.info

  sem set_Regex_info val =
  | RepeatStarRegex target ->
    RepeatStarRegex
      { target
        with
        info =
          val }

end

lang RepeatQuestionRegexAst = SelfhostBaseAst
  type RepeatQuestionRegexRecord = {info: Info, left: Regex}

  syn Regex =
  | RepeatQuestionRegex RepeatQuestionRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RepeatQuestionRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        (acc, { x
          with
          left =
            left })
      else
        never
    with
      (acc, x)
    then
      (acc, RepeatQuestionRegex
        x)
    else
      never

  sem get_Regex_info =
  | RepeatQuestionRegex target ->
    target.info

  sem set_Regex_info val =
  | RepeatQuestionRegex target ->
    RepeatQuestionRegex
      { target
        with
        info =
          val }

end

lang NamedRegexAst = SelfhostBaseAst
  type NamedRegexRecord = {info: Info, name: {i: Info, v: String}, right: Regex}

  syn Regex =
  | NamedRegex NamedRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | NamedRegex x ->
    match
      match
        let right =
          x.right
        in
        f
          acc
          right
      with
        (acc, right)
      then
        (acc, { x
          with
          right =
            right })
      else
        never
    with
      (acc, x)
    then
      (acc, NamedRegex
        x)
    else
      never

  sem get_Regex_info =
  | NamedRegex target ->
    target.info

  sem set_Regex_info val =
  | NamedRegex target ->
    NamedRegex
      { target
        with
        info =
          val }

end

lang AlternativeRegexAst = SelfhostBaseAst
  type AlternativeRegexRecord = {info: Info, left: Regex, right: Regex}

  syn Regex =
  | AlternativeRegex AlternativeRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | AlternativeRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        then
          (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
        else
          never
      else
        never
    with
      (acc, x)
    then
      (acc, AlternativeRegex
        x)
    else
      never

  sem get_Regex_info =
  | AlternativeRegex target ->
    target.info

  sem set_Regex_info val =
  | AlternativeRegex target ->
    AlternativeRegex
      { target
        with
        info =
          val }

end

lang ConcatRegexAst = SelfhostBaseAst
  type ConcatRegexRecord = {info: Info, left: Regex, right: Regex}

  syn Regex =
  | ConcatRegex ConcatRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | ConcatRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        then
          (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
        else
          never
      else
        never
    with
      (acc, x)
    then
      (acc, ConcatRegex
        x)
    else
      never

  sem get_Regex_info =
  | ConcatRegex target ->
    target.info

  sem set_Regex_info val =
  | ConcatRegex target ->
    ConcatRegex
      { target
        with
        info =
          val }

end

lang AppExprAst = SelfhostBaseAst
  type AppExprRecord = {info: Info, left: Expr, right: Expr}

  syn Expr =
  | AppExpr AppExprRecord

  sem smapAccumL_Expr_Expr f acc =
  | AppExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        then
          (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
        else
          never
      else
        never
    with
      (acc, x)
    then
      (acc, AppExpr
        x)
    else
      never

  sem get_Expr_info =
  | AppExpr target ->
    target.info

  sem set_Expr_info val =
  | AppExpr target ->
    AppExpr
      { target
        with
        info =
          val }

end

lang ConExprAst = SelfhostBaseAst
  type ConExprRecord = {info: Info, name: {i: Info, v: Name}}

  syn Expr =
  | ConExpr ConExprRecord

  sem get_Expr_info =
  | ConExpr target ->
    target.info

  sem set_Expr_info val =
  | ConExpr target ->
    ConExpr
      { target
        with
        info =
          val }

end

lang StringExprAst = SelfhostBaseAst
  type StringExprRecord = {val: {i: Info, v: String}, info: Info}

  syn Expr =
  | StringExpr StringExprRecord

  sem get_Expr_info =
  | StringExpr target ->
    target.info

  sem set_Expr_info val =
  | StringExpr target ->
    StringExpr
      { target
        with
        info =
          val }

end

lang VariableExprAst = SelfhostBaseAst
  type VariableExprRecord = {info: Info, name: {i: Info, v: Name}}

  syn Expr =
  | VariableExpr VariableExprRecord

  sem get_Expr_info =
  | VariableExpr target ->
    target.info

  sem set_Expr_info val =
  | VariableExpr target ->
    VariableExpr
      { target
        with
        info =
          val }

end

lang RecordExprAst = SelfhostBaseAst
  type RecordExprRecord = {info: Info, fields: [{val: Expr, name: {i: Info, v: String}}]}

  syn Expr =
  | RecordExpr RecordExprRecord

  sem smapAccumL_Expr_Expr f acc =
  | RecordExpr x ->
    match
      match
        let fields =
          x.fields
        in
        mapAccumL
          (lam acc1.
             lam x1: {val: Expr, name: {i: Info, v: String}}.
               match
                 let val =
                   x1.val
                 in
                 f
                   acc1
                   val
               with
                 (acc1, val)
               then
                 (acc1, { x1
                   with
                   val =
                     val })
               else
                 never)
          acc
          fields
      with
        (acc, fields)
      then
        (acc, { x
          with
          fields =
            fields })
      else
        never
    with
      (acc, x)
    then
      (acc, RecordExpr
        x)
    else
      never

  sem get_Expr_info =
  | RecordExpr target ->
    target.info

  sem set_Expr_info val =
  | RecordExpr target ->
    RecordExpr
      { target
        with
        info =
          val }

end

lang BadFileAst = SelfhostBaseAst
  type BadFileRecord = {info: Info}

  syn File =
  | BadFile BadFileRecord

  sem get_File_info =
  | BadFile target ->
    target.info

  sem set_File_info val =
  | BadFile target ->
    BadFile
      { target
        with
        info =
          val }

end

lang BadDeclAst = SelfhostBaseAst
  type BadDeclRecord = {info: Info}

  syn Decl =
  | BadDecl BadDeclRecord

  sem get_Decl_info =
  | BadDecl target ->
    target.info

  sem set_Decl_info val =
  | BadDecl target ->
    BadDecl
      { target
        with
        info =
          val }

end

lang BadRegexAst = SelfhostBaseAst
  type BadRegexRecord = {info: Info}

  syn Regex =
  | BadRegex BadRegexRecord

  sem get_Regex_info =
  | BadRegex target ->
    target.info

  sem set_Regex_info val =
  | BadRegex target ->
    BadRegex
      { target
        with
        info =
          val }

end

lang BadExprAst = SelfhostBaseAst
  type BadExprRecord = {info: Info}

  syn Expr =
  | BadExpr BadExprRecord

  sem get_Expr_info =
  | BadExpr target ->
    target.info

  sem set_Expr_info val =
  | BadExpr target ->
    BadExpr
      { target
        with
        info =
          val }

end

lang SelfhostAst = FileAst + StartDeclAst + IncludeDeclAst + TypeDeclAst + TokenDeclAst + PrecedenceTableDeclAst + ProductionDeclAst + RecordRegexAst + EmptyRegexAst + LiteralRegexAst + TokenRegexAst + RepeatPlusRegexAst + RepeatStarRegexAst + RepeatQuestionRegexAst + NamedRegexAst + AlternativeRegexAst + ConcatRegexAst + AppExprAst + ConExprAst + StringExprAst + VariableExprAst + RecordExprAst + BadFileAst + BadDeclAst + BadRegexAst + BadExprAst



end

lang FileOpBase = SelfhostBaseAst

  syn FileOp lstyle rstyle =

  sem topAllowed_FileOp : all lstyle. all rstyle. (((FileOp) (lstyle)) (rstyle)) -> (Bool)
  sem topAllowed_FileOp =
  | _ ->
    true

  sem leftAllowed_FileOp : all lstyle. all style. all rstyle. ({child: ((FileOp) (lstyle)) (rstyle), parent: ((FileOp) (LOpen)) (style)}) -> (Bool)
  sem leftAllowed_FileOp =
  | _ ->
    true

  sem rightAllowed_FileOp : all style. all lstyle. all rstyle. ({child: ((FileOp) (lstyle)) (rstyle), parent: ((FileOp) (style)) (ROpen)}) -> (Bool)
  sem rightAllowed_FileOp =
  | _ ->
    true

  sem groupingsAllowed_FileOp : all lstyle. all rstyle. ((((FileOp) (lstyle)) (ROpen), ((FileOp) (LOpen)) (rstyle))) -> (AllowedDirection)
  sem groupingsAllowed_FileOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_FileOp : all lstyle. all rstyle. (((FileOp) (lstyle)) (rstyle)) -> (AllowedDirection)
  sem parenAllowed_FileOp =
  | _ ->
    GEither
      {}

  sem get_FileOp_info : all lstyle. all rstyle. (((FileOp) (lstyle)) (rstyle)) -> (Info)

  sem get_FileOp_terms : all lstyle. all rstyle. (((FileOp) (lstyle)) (rstyle)) -> ([Info])

  sem unsplit_FileOp : ((PermanentNode) (FileOp)) -> ((Info, File))

end

lang DeclOpBase = SelfhostBaseAst

  syn DeclOp lstyle rstyle =

  sem topAllowed_DeclOp : all lstyle. all rstyle. (((DeclOp) (lstyle)) (rstyle)) -> (Bool)
  sem topAllowed_DeclOp =
  | _ ->
    true

  sem leftAllowed_DeclOp : all lstyle. all style. all rstyle. ({child: ((DeclOp) (lstyle)) (rstyle), parent: ((DeclOp) (LOpen)) (style)}) -> (Bool)
  sem leftAllowed_DeclOp =
  | _ ->
    true

  sem rightAllowed_DeclOp : all style. all lstyle. all rstyle. ({child: ((DeclOp) (lstyle)) (rstyle), parent: ((DeclOp) (style)) (ROpen)}) -> (Bool)
  sem rightAllowed_DeclOp =
  | _ ->
    true

  sem groupingsAllowed_DeclOp : all lstyle. all rstyle. ((((DeclOp) (lstyle)) (ROpen), ((DeclOp) (LOpen)) (rstyle))) -> (AllowedDirection)
  sem groupingsAllowed_DeclOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_DeclOp : all lstyle. all rstyle. (((DeclOp) (lstyle)) (rstyle)) -> (AllowedDirection)
  sem parenAllowed_DeclOp =
  | _ ->
    GEither
      {}

  sem get_DeclOp_info : all lstyle. all rstyle. (((DeclOp) (lstyle)) (rstyle)) -> (Info)

  sem get_DeclOp_terms : all lstyle. all rstyle. (((DeclOp) (lstyle)) (rstyle)) -> ([Info])

  sem unsplit_DeclOp : ((PermanentNode) (DeclOp)) -> ((Info, Decl))

end

lang RegexOpBase = SelfhostBaseAst

  syn RegexOp lstyle rstyle =

  sem topAllowed_RegexOp : all lstyle. all rstyle. (((RegexOp) (lstyle)) (rstyle)) -> (Bool)
  sem topAllowed_RegexOp =
  | _ ->
    true

  sem leftAllowed_RegexOp : all lstyle. all style. all rstyle. ({child: ((RegexOp) (lstyle)) (rstyle), parent: ((RegexOp) (LOpen)) (style)}) -> (Bool)
  sem leftAllowed_RegexOp =
  | _ ->
    true

  sem rightAllowed_RegexOp : all style. all lstyle. all rstyle. ({child: ((RegexOp) (lstyle)) (rstyle), parent: ((RegexOp) (style)) (ROpen)}) -> (Bool)
  sem rightAllowed_RegexOp =
  | _ ->
    true

  sem groupingsAllowed_RegexOp : all lstyle. all rstyle. ((((RegexOp) (lstyle)) (ROpen), ((RegexOp) (LOpen)) (rstyle))) -> (AllowedDirection)
  sem groupingsAllowed_RegexOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_RegexOp : all lstyle. all rstyle. (((RegexOp) (lstyle)) (rstyle)) -> (AllowedDirection)
  sem parenAllowed_RegexOp =
  | _ ->
    GEither
      {}

  sem get_RegexOp_info : all lstyle. all rstyle. (((RegexOp) (lstyle)) (rstyle)) -> (Info)

  sem get_RegexOp_terms : all lstyle. all rstyle. (((RegexOp) (lstyle)) (rstyle)) -> ([Info])

  sem unsplit_RegexOp : ((PermanentNode) (RegexOp)) -> ((Info, Regex))

end

lang ExprOpBase = SelfhostBaseAst

  syn ExprOp lstyle rstyle =

  sem topAllowed_ExprOp : all lstyle. all rstyle. (((ExprOp) (lstyle)) (rstyle)) -> (Bool)
  sem topAllowed_ExprOp =
  | _ ->
    true

  sem leftAllowed_ExprOp : all lstyle. all style. all rstyle. ({child: ((ExprOp) (lstyle)) (rstyle), parent: ((ExprOp) (LOpen)) (style)}) -> (Bool)
  sem leftAllowed_ExprOp =
  | _ ->
    true

  sem rightAllowed_ExprOp : all style. all lstyle. all rstyle. ({child: ((ExprOp) (lstyle)) (rstyle), parent: ((ExprOp) (style)) (ROpen)}) -> (Bool)
  sem rightAllowed_ExprOp =
  | _ ->
    true

  sem groupingsAllowed_ExprOp : all lstyle. all rstyle. ((((ExprOp) (lstyle)) (ROpen), ((ExprOp) (LOpen)) (rstyle))) -> (AllowedDirection)
  sem groupingsAllowed_ExprOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_ExprOp : all lstyle. all rstyle. (((ExprOp) (lstyle)) (rstyle)) -> (AllowedDirection)
  sem parenAllowed_ExprOp =
  | _ ->
    GEither
      {}

  sem get_ExprOp_info : all lstyle. all rstyle. (((ExprOp) (lstyle)) (rstyle)) -> (Info)

  sem get_ExprOp_terms : all lstyle. all rstyle. (((ExprOp) (lstyle)) (rstyle)) -> ([Info])

  sem unsplit_ExprOp : ((PermanentNode) (ExprOp)) -> ((Info, Expr))

end

lang FileOp = FileOpBase + FileAst

  syn FileOp lstyle rstyle =
  | FileOp {name: [{i: Info, v: String}], decls: [Decl], __br_info: Info, __br_terms: [Info]}

  sem get_FileOp_info =
  | FileOp x ->
    x.__br_info

  sem get_FileOp_terms =
  | FileOp x ->
    x.__br_terms

  sem unsplit_FileOp =
  | AtomP {self = FileOp x} ->
    (x.__br_info, File
      { info =
          x.__br_info,
        decls =
          x.decls,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang StartDeclOp = DeclOpBase + StartDeclAst

  syn DeclOp lstyle rstyle =
  | StartDeclOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}

  sem get_DeclOp_info =
  | StartDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | StartDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = StartDeclOp x} ->
    (x.__br_info, StartDecl
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang IncludeDeclOp = DeclOpBase + IncludeDeclAst

  syn DeclOp lstyle rstyle =
  | IncludeDeclOp {path: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}

  sem get_DeclOp_info =
  | IncludeDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | IncludeDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = IncludeDeclOp x} ->
    (x.__br_info, IncludeDecl
      { info =
          x.__br_info,
        path =
          match
            x.path
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang TypeDeclOp = DeclOpBase + TypeDeclAst

  syn DeclOp lstyle rstyle =
  | TypeDeclOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]}

  sem get_DeclOp_info =
  | TypeDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | TypeDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = TypeDeclOp x} ->
    (x.__br_info, TypeDecl
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never,
        properties =
          x.properties })

end

lang TokenDeclOp = DeclOpBase + TokenDeclAst

  syn DeclOp lstyle rstyle =
  | TokenDeclOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]}

  sem get_DeclOp_info =
  | TokenDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | TokenDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = TokenDeclOp x} ->
    (x.__br_info, TokenDecl
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            Some
              x1
          else
            None
              {},
        properties =
          x.properties })

end

lang PrecedenceTableDeclOp = DeclOpBase + PrecedenceTableDeclAst

  syn DeclOp lstyle rstyle =
  | PrecedenceTableDeclOp {levels: [{noeq: (Option) (Info), operators: [{i: Info, v: Name}]}], __br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]}

  sem get_DeclOp_info =
  | PrecedenceTableDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | PrecedenceTableDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = PrecedenceTableDeclOp x} ->
    (x.__br_info, PrecedenceTableDecl
      { info =
          x.__br_info,
        levels =
          x.levels,
        exceptions =
          x.exceptions })

end

lang ProductionDeclOp = DeclOpBase + ProductionDeclAst

  syn DeclOp lstyle rstyle =
  | ProductionDeclOp {nt: [{i: Info, v: Name}], kinf: [Info], name: [{i: Info, v: Name}], assoc: [{i: Info, v: String}], kpref: [Info], kprod: [Info], regex: [Regex], kpostf: [Info], __br_info: Info, __br_terms: [Info]}

  sem get_DeclOp_info =
  | ProductionDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | ProductionDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = ProductionDeclOp x} ->
    (x.__br_info, ProductionDecl
      { info =
          x.__br_info,
        nt =
          match
            x.nt
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never,
        name =
          match
            x.name
          with
            [ x2 ] ++ _ ++ ""
          then
            x2
          else
            never,
        kinf =
          match
            x.kinf
          with
            [ x3 ] ++ _ ++ ""
          then
            Some
              x3
          else
            None
              {},
        kpref =
          match
            x.kpref
          with
            [ x4 ] ++ _ ++ ""
          then
            Some
              x4
          else
            None
              {},
        kprod =
          match
            x.kprod
          with
            [ x5 ] ++ _ ++ ""
          then
            Some
              x5
          else
            None
              {},
        kpostf =
          match
            x.kpostf
          with
            [ x6 ] ++ _ ++ ""
          then
            Some
              x6
          else
            None
              {},
        assoc =
          match
            x.assoc
          with
            [ x7 ] ++ _ ++ ""
          then
            Some
              x7
          else
            None
              {},
        regex =
          match
            x.regex
          with
            [ x8 ] ++ _ ++ ""
          then
            x8
          else
            never })

end

lang RecordRegexOp = RegexOpBase + RecordRegexAst

  syn RegexOp lstyle rstyle =
  | RecordRegexOp {regex: [Regex], __br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | RecordRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RecordRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = RecordRegexOp x} ->
    (x.__br_info, RecordRegex
      { info =
          x.__br_info,
        regex =
          match
            x.regex
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang EmptyRegexOp = RegexOpBase + EmptyRegexAst

  syn RegexOp lstyle rstyle =
  | EmptyRegexOp {__br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | EmptyRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | EmptyRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = EmptyRegexOp x} ->
    (x.__br_info, EmptyRegex
      { info =
          x.__br_info })

end

lang LiteralRegexOp = RegexOpBase + LiteralRegexAst

  syn RegexOp lstyle rstyle =
  | LiteralRegexOp {val: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | LiteralRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | LiteralRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = LiteralRegexOp x} ->
    (x.__br_info, LiteralRegex
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang TokenRegexOp = RegexOpBase + TokenRegexAst

  syn RegexOp lstyle rstyle =
  | TokenRegexOp {arg: [Expr], name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | TokenRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | TokenRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = TokenRegexOp x} ->
    (x.__br_info, TokenRegex
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never,
        arg =
          match
            x.arg
          with
            [ x2 ] ++ _ ++ ""
          then
            Some
              x2
          else
            None
              {} })

end

lang RepeatPlusRegexOp = RegexOpBase + RepeatPlusRegexAst

  syn RegexOp lstyle rstyle =
  | RepeatPlusRegexOp {__br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | RepeatPlusRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RepeatPlusRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PostfixP {self = RepeatPlusRegexOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        l
    with
      (linfo, l)
    then
      let info =
        mergeInfo
          linfo
          (x.__br_info)
      in
      (info, RepeatPlusRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never })
    else
      never

end

lang RepeatStarRegexOp = RegexOpBase + RepeatStarRegexAst

  syn RegexOp lstyle rstyle =
  | RepeatStarRegexOp {__br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | RepeatStarRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RepeatStarRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PostfixP {self = RepeatStarRegexOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        l
    with
      (linfo, l)
    then
      let info =
        mergeInfo
          linfo
          (x.__br_info)
      in
      (info, RepeatStarRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never })
    else
      never

end

lang RepeatQuestionRegexOp = RegexOpBase + RepeatQuestionRegexAst

  syn RegexOp lstyle rstyle =
  | RepeatQuestionRegexOp {__br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | RepeatQuestionRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RepeatQuestionRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PostfixP {self = RepeatQuestionRegexOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        l
    with
      (linfo, l)
    then
      let info =
        mergeInfo
          linfo
          (x.__br_info)
      in
      (info, RepeatQuestionRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never })
    else
      never

end

lang NamedRegexOp = RegexOpBase + NamedRegexAst

  syn RegexOp lstyle rstyle =
  | NamedRegexOp {name: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | NamedRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | NamedRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PrefixP {self = NamedRegexOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        r
    with
      (rinfo, r)
    then
      let info =
        mergeInfo
          (x.__br_info)
          rinfo
      in
      (info, NamedRegex
        { info =
            info,
          name =
            match
              x.name
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

end

lang AlternativeRegexOp = RegexOpBase + AlternativeRegexAst

  syn RegexOp lstyle rstyle =
  | AlternativeRegexOp {__br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | AlternativeRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | AlternativeRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | InfixP {self = AlternativeRegexOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_RegexOp
        l, unsplit_RegexOp
        r)
    with
      ((linfo, l), (rinfo, r))
    then
      let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AlternativeRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

  sem groupingsAllowed_RegexOp =
  | (AlternativeRegexOp _, AlternativeRegexOp _) ->
    GLeft
      {}

end

lang ConcatRegexOp = RegexOpBase + ConcatRegexAst

  syn RegexOp lstyle rstyle =
  | ConcatRegexOp {__br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | ConcatRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | ConcatRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | InfixP {self = ConcatRegexOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_RegexOp
        l, unsplit_RegexOp
        r)
    with
      ((linfo, l), (rinfo, r))
    then
      let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, ConcatRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

  sem groupingsAllowed_RegexOp =
  | (ConcatRegexOp _, ConcatRegexOp _) ->
    GLeft
      {}

end

lang AppExprOp = ExprOpBase + AppExprAst

  syn ExprOp lstyle rstyle =
  | AppExprOp {__br_info: Info, __br_terms: [Info]}

  sem get_ExprOp_info =
  | AppExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | AppExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | InfixP {self = AppExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_ExprOp
        l, unsplit_ExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    then
      let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AppExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

  sem groupingsAllowed_ExprOp =
  | (AppExprOp _, AppExprOp _) ->
    GLeft
      {}

end

lang ConExprOp = ExprOpBase + ConExprAst

  syn ExprOp lstyle rstyle =
  | ConExprOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}

  sem get_ExprOp_info =
  | ConExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | ConExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = ConExprOp x} ->
    (x.__br_info, ConExpr
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang StringExprOp = ExprOpBase + StringExprAst

  syn ExprOp lstyle rstyle =
  | StringExprOp {val: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}

  sem get_ExprOp_info =
  | StringExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | StringExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = StringExprOp x} ->
    (x.__br_info, StringExpr
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang VariableExprOp = ExprOpBase + VariableExprAst

  syn ExprOp lstyle rstyle =
  | VariableExprOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}

  sem get_ExprOp_info =
  | VariableExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | VariableExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = VariableExprOp x} ->
    (x.__br_info, VariableExpr
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang RecordExprOp = ExprOpBase + RecordExprAst

  syn ExprOp lstyle rstyle =
  | RecordExprOp {fields: [{val: Expr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]}

  sem get_ExprOp_info =
  | RecordExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | RecordExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = RecordExprOp x} ->
    (x.__br_info, RecordExpr
      { info =
          x.__br_info,
        fields =
          x.fields })

end

lang RegexGrouping = RegexOpBase

  syn RegexOp lstyle rstyle =
  | RegexGrouping {inner: Regex, __br_info: Info, __br_terms: [Info]}

  sem get_RegexOp_info =
  | RegexGrouping x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RegexGrouping x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = RegexGrouping x} ->
    (x.__br_info, x.inner)

end

lang ExprGrouping = ExprOpBase

  syn ExprOp lstyle rstyle =
  | ExprGrouping {inner: Expr, __br_info: Info, __br_terms: [Info]}

  sem get_ExprOp_info =
  | ExprGrouping x ->
    x.__br_info

  sem get_ExprOp_terms =
  | ExprGrouping x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = ExprGrouping x} ->
    (x.__br_info, x.inner)

end

lang ParseSelfhost = FileOp + StartDeclOp + IncludeDeclOp + TypeDeclOp + TokenDeclOp + PrecedenceTableDeclOp + ProductionDeclOp + RecordRegexOp + EmptyRegexOp + LiteralRegexOp + TokenRegexOp + RepeatPlusRegexOp + RepeatStarRegexOp + RepeatQuestionRegexOp + NamedRegexOp + AlternativeRegexOp + ConcatRegexOp + AppExprOp + ConExprOp + StringExprOp + VariableExprOp + RecordExprOp + RegexGrouping + ExprGrouping + BadFileAst + BadDeclAst + BadRegexAst + BadExprAst + LL1Parser + SemiTokenParser + CommaTokenParser + WhitespaceParser + LIdentTokenParser + LineCommentParser + StringTokenParser + UIdentTokenParser + BracketTokenParser + OperatorTokenParser + MultilineCommentParser




  sem groupingsAllowed_RegexOp =
  | (NamedRegexOp _, RepeatPlusRegexOp _) ->
    GLeft
      {}
  | (AlternativeRegexOp _, RepeatPlusRegexOp _) ->
    GRight
      {}
  | (ConcatRegexOp _, RepeatPlusRegexOp _) ->
    GRight
      {}
  | (NamedRegexOp _, RepeatStarRegexOp _) ->
    GLeft
      {}
  | (AlternativeRegexOp _, RepeatStarRegexOp _) ->
    GRight
      {}
  | (ConcatRegexOp _, RepeatStarRegexOp _) ->
    GRight
      {}
  | (NamedRegexOp _, RepeatQuestionRegexOp _) ->
    GLeft
      {}
  | (AlternativeRegexOp _, RepeatQuestionRegexOp _) ->
    GRight
      {}
  | (ConcatRegexOp _, RepeatQuestionRegexOp _) ->
    GRight
      {}
  | (NamedRegexOp _, AlternativeRegexOp _) ->
    GLeft
      {}
  | (NamedRegexOp _, ConcatRegexOp _) ->
    GLeft
      {}
  | (AlternativeRegexOp _, ConcatRegexOp _) ->
    GRight
      {}
  | (ConcatRegexOp _, AlternativeRegexOp _) ->
    GLeft
      {}


end



let _table = use ParseSelfhost in let target =
  genParsingTable
    (let #var"File" =
       nameSym
         "File"
     in
     let #var"Decl" =
       nameSym
         "Decl"
     in
     let #var"Regex" =
       nameSym
         "Regex"
     in
     let #var"Expr" =
       nameSym
         "Expr"
     in
     let #var"FileAtom" =
       nameSym
         "FileAtom"
     in
     let #var"FileInfix" =
       nameSym
         "FileInfix"
     in
     let #var"FilePrefix" =
       nameSym
         "FilePrefix"
     in
     let #var"FilePostfix" =
       nameSym
         "FilePostfix"
     in
     let #var"DeclAtom" =
       nameSym
         "DeclAtom"
     in
     let #var"DeclInfix" =
       nameSym
         "DeclInfix"
     in
     let #var"DeclPrefix" =
       nameSym
         "DeclPrefix"
     in
     let #var"DeclPostfix" =
       nameSym
         "DeclPostfix"
     in
     let #var"RegexAtom" =
       nameSym
         "RegexAtom"
     in
     let #var"RegexInfix" =
       nameSym
         "RegexInfix"
     in
     let #var"RegexPrefix" =
       nameSym
         "RegexPrefix"
     in
     let #var"RegexPostfix" =
       nameSym
         "RegexPostfix"
     in
     let #var"ExprAtom" =
       nameSym
         "ExprAtom"
     in
     let #var"ExprInfix" =
       nameSym
         "ExprInfix"
     in
     let #var"ExprPrefix" =
       nameSym
         "ExprPrefix"
     in
     let #var"ExprPostfix" =
       nameSym
         "ExprPostfix"
     in
     let kleene =
       nameSym
         "kleene"
     in
     let kleene1 =
       nameSym
         "kleene"
     in
     let alt =
       nameSym
         "alt"
     in
     let alt1 =
       nameSym
         "alt"
     in
     let kleene2 =
       nameSym
         "kleene"
     in
     let alt2 =
       nameSym
         "alt"
     in
     let alt3 =
       nameSym
         "alt"
     in
     let kleene3 =
       nameSym
         "kleene"
     in
     let kleene4 =
       nameSym
         "kleene"
     in
     let kleene5 =
       nameSym
         "kleene"
     in
     let kleene6 =
       nameSym
         "kleene"
     in
     let kleene7 =
       nameSym
         "kleene"
     in
     let alt4 =
       nameSym
         "alt"
     in
     let alt5 =
       nameSym
         "alt"
     in
     let alt6 =
       nameSym
         "alt"
     in
     let alt7 =
       nameSym
         "alt"
     in
     let kleene8 =
       nameSym
         "kleene"
     in
     let alt8 =
       nameSym
         "alt"
     in
     let #var"File_lclosed" =
       nameSym
         "File_lclosed"
     in
     let #var"File_lopen" =
       nameSym
         "File_lopen"
     in
     let #var"Decl_lclosed" =
       nameSym
         "Decl_lclosed"
     in
     let #var"Decl_lopen" =
       nameSym
         "Decl_lopen"
     in
     let #var"Regex_lclosed" =
       nameSym
         "Regex_lclosed"
     in
     let #var"Regex_lopen" =
       nameSym
         "Regex_lopen"
     in
     let #var"Expr_lclosed" =
       nameSym
         "Expr_lclosed"
     in
     let #var"Expr_lopen" =
       nameSym
         "Expr_lopen"
     in
     { start =
         #var"File",
       productions =
         let config =
           { topAllowed =
               #frozen"topAllowed_FileOp",
             leftAllowed =
               #frozen"leftAllowed_FileOp",
             rightAllowed =
               #frozen"rightAllowed_FileOp",
             parenAllowed =
               #frozen"parenAllowed_FileOp",
             groupingsAllowed =
               #frozen"groupingsAllowed_FileOp" }
         in
         let reportConfig =
           { topAllowed =
               #frozen"topAllowed_FileOp",
             parenAllowed =
               #frozen"parenAllowed_FileOp",
             terminalInfos =
               #frozen"get_FileOp_terms",
             getInfo =
               #frozen"get_FileOp_info",
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addFileOpAtom =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config
                      x33)
                   st
         in
         let addFileOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_FileOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let addFileOpPrefix =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config
                      x33)
                   st
         in
         let addFileOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_FileOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let finalizeFileOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res60 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig
                            (p.content)
                            tops
                        in
                        let res60: (Info, File) =
                          unsplit_FileOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res60
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res60.#label"0", BadFile
                              { info =
                                  res60.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished File")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadFile
                   { info =
                       NoInfo
                         {} })
                 res60
         in
         let config1 =
           { topAllowed =
               #frozen"topAllowed_DeclOp",
             leftAllowed =
               #frozen"leftAllowed_DeclOp",
             rightAllowed =
               #frozen"rightAllowed_DeclOp",
             parenAllowed =
               #frozen"parenAllowed_DeclOp",
             groupingsAllowed =
               #frozen"groupingsAllowed_DeclOp" }
         in
         let reportConfig1 =
           { topAllowed =
               #frozen"topAllowed_DeclOp",
             parenAllowed =
               #frozen"parenAllowed_DeclOp",
             terminalInfos =
               #frozen"get_DeclOp_terms",
             getInfo =
               #frozen"get_DeclOp_info",
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addDeclOpAtom =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config1
                      x33)
                   st
         in
         let addDeclOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config1
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_DeclOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let addDeclOpPrefix =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config1
                      x33)
                   st
         in
         let addDeclOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config1
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_DeclOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let finalizeDeclOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res60 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config1
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig1
                            (p.content)
                            tops
                        in
                        let res60: (Info, Decl) =
                          unsplit_DeclOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res60
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res60.#label"0", BadDecl
                              { info =
                                  res60.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished Decl")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadDecl
                   { info =
                       NoInfo
                         {} })
                 res60
         in
         let config2 =
           { topAllowed =
               #frozen"topAllowed_RegexOp",
             leftAllowed =
               #frozen"leftAllowed_RegexOp",
             rightAllowed =
               #frozen"rightAllowed_RegexOp",
             parenAllowed =
               #frozen"parenAllowed_RegexOp",
             groupingsAllowed =
               #frozen"groupingsAllowed_RegexOp" }
         in
         let reportConfig2 =
           { topAllowed =
               #frozen"topAllowed_RegexOp",
             parenAllowed =
               #frozen"parenAllowed_RegexOp",
             terminalInfos =
               #frozen"get_RegexOp_terms",
             getInfo =
               #frozen"get_RegexOp_info",
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addRegexOpAtom =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config2
                      x33)
                   st
         in
         let addRegexOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config2
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_RegexOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let addRegexOpPrefix =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config2
                      x33)
                   st
         in
         let addRegexOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config2
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_RegexOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let finalizeRegexOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res60 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config2
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig2
                            (p.content)
                            tops
                        in
                        let res60: (Info, Regex) =
                          unsplit_RegexOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res60
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res60.#label"0", BadRegex
                              { info =
                                  res60.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished Regex")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadRegex
                   { info =
                       NoInfo
                         {} })
                 res60
         in
         let config3 =
           { topAllowed =
               #frozen"topAllowed_ExprOp",
             leftAllowed =
               #frozen"leftAllowed_ExprOp",
             rightAllowed =
               #frozen"rightAllowed_ExprOp",
             parenAllowed =
               #frozen"parenAllowed_ExprOp",
             groupingsAllowed =
               #frozen"groupingsAllowed_ExprOp" }
         in
         let reportConfig3 =
           { topAllowed =
               #frozen"topAllowed_ExprOp",
             parenAllowed =
               #frozen"parenAllowed_ExprOp",
             terminalInfos =
               #frozen"get_ExprOp_terms",
             getInfo =
               #frozen"get_ExprOp_info",
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addExprOpAtom =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config3
                      x33)
                   st
         in
         let addExprOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config3
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_ExprOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let addExprOpPrefix =
           lam #var"".
             lam x33.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config3
                      x33)
                   st
         in
         let addExprOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x33.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config3
                       x33
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_ExprOp_info
                               x33, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   None
                     {}
         in
         let finalizeExprOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res60 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config3
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig3
                            (p.content)
                            tops
                        in
                        let res60: (Info, Expr) =
                          unsplit_ExprOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res60
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res60.#label"0", BadExpr
                              { info =
                                  res60.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished Expr")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadExpr
                   { info =
                       NoInfo
                         {} })
                 res60
         in
         [ { nt =
               kleene,
             label =
               {},
             rhs =
               [ ntSym
                   #var"Decl",
                 ntSym
                   kleene ],
             action =
               lam state: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res.
                   match
                     res
                   with
                     [ UserSym ntVal,
                       UserSym val ]
                   then
                     let ntVal: (Info, Decl) =
                       fromDyn
                         ntVal
                     in
                     let val: {decls: [Decl], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val
                     in
                     asDyn
                       { __br_terms =
                           val.__br_terms,
                         decls =
                           concat
                             [ ntVal.#label"1" ]
                             (val.decls),
                         __br_info =
                           mergeInfo
                             (ntVal.#label"0")
                             (val.__br_info) }
                   else
                     never },
           { nt =
               kleene,
             label =
               {},
             rhs =
               "",
             action =
               lam state1: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res1.
                   match
                     res1
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         decls =
                           "",
                         __br_info =
                           NoInfo
                             {} }
                   else
                     never },
           { nt =
               #var"FileAtom",
             label =
               {},
             rhs =
               [ litSym
                   "language",
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   #var"Decl",
                 ntSym
                   kleene ],
             action =
               lam state2: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res2.
                   match
                     res2
                   with
                     [ LitParsed l,
                       TokParsed (UIdentTok x),
                       UserSym ntVal1,
                       UserSym val ]
                   then
                     let ntVal1: (Info, Decl) =
                       fromDyn
                         ntVal1
                     in
                     let val: {decls: [Decl], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val
                     in
                     asDyn
                       (FileOp
                          { __br_terms =
                              join
                                [ [ l.info ],
                                  [ x.info ],
                                  val.__br_terms ],
                            decls =
                              concat
                                [ ntVal1.#label"1" ]
                                (val.decls),
                            __br_info =
                              foldl
                                mergeInfo
                                (l.info)
                                [ x.info,
                                  ntVal1.#label"0",
                                  val.__br_info ],
                            name =
                              [ { v =
                                    x.val,
                                  i =
                                    x.info } ] })
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "start",
                 tokSym
                   (UIdentRepr
                      {}) ],
             action =
               lam state3: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res3.
                   match
                     res3
                   with
                     [ LitParsed l1,
                       TokParsed (UIdentTok x1) ]
                   then
                     asDyn
                       (StartDeclOp
                          { __br_terms =
                              concat
                                [ l1.info ]
                                [ x1.info ],
                            __br_info =
                              mergeInfo
                                (l1.info)
                                (x1.info),
                            name =
                              [ { v =
                                    nameNoSym
                                      (x1.val),
                                  i =
                                    x1.info } ] })
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "include",
                 tokSym
                   (StringRepr
                      {}) ],
             action =
               lam state4: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res4.
                   match
                     res4
                   with
                     [ LitParsed l2,
                       TokParsed (StringTok x2) ]
                   then
                     asDyn
                       (IncludeDeclOp
                          { __br_terms =
                              concat
                                [ l2.info ]
                                [ x2.info ],
                            __br_info =
                              mergeInfo
                                (l2.info)
                                (x2.info),
                            path =
                              [ { v =
                                    x2.val,
                                  i =
                                    x2.info } ] })
                   else
                     never },
           { nt =
               kleene1,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 litSym
                   ",",
                 ntSym
                   kleene1 ],
             action =
               lam state5: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res5.
                   match
                     res5
                   with
                     [ TokParsed (LIdentTok x3),
                       LitParsed l3,
                       UserSym ntVal2,
                       LitParsed l4,
                       UserSym val1 ]
                   then
                     let ntVal2: (Info, Expr) =
                       fromDyn
                         ntVal2
                     in
                     let val1: {__br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]} =
                       fromDyn
                         val1
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ x3.info ],
                               [ l3.info ],
                               [ l4.info ],
                               val1.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (x3.info)
                             [ l3.info,
                               ntVal2.#label"0",
                               l4.info,
                               val1.__br_info ],
                         properties =
                           concat
                             [ { val =
                                   match
                                     [ ntVal2.#label"1" ]
                                   with
                                     [ x4 ] ++ _ ++ ""
                                   then
                                     x4
                                   else
                                     never,
                                 name =
                                   match
                                     [ { v =
                                           x3.val,
                                         i =
                                           x3.info } ]
                                   with
                                     [ x5 ] ++ _ ++ ""
                                   then
                                     x5
                                   else
                                     never } ]
                             (val1.properties) }
                   else
                     never },
           { nt =
               kleene1,
             label =
               {},
             rhs =
               "",
             action =
               lam state6: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res6.
                   match
                     res6
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         properties =
                           "" }
                   else
                     never },
           { nt =
               alt,
             label =
               {},
             rhs =
               "",
             action =
               lam state7: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res7.
                   match
                     res7
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         properties =
                           "" }
                   else
                     never },
           { nt =
               alt,
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   kleene1,
                 litSym
                   "}" ],
             action =
               lam state8: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res8.
                   match
                     res8
                   with
                     [ LitParsed l5,
                       UserSym val1,
                       LitParsed l6 ]
                   then
                     let val1: {__br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]} =
                       fromDyn
                         val1
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ l5.info ],
                               val1.__br_terms,
                               [ l6.info ] ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l5.info)
                             [ val1.__br_info,
                               l6.info ],
                         properties =
                           val1.properties }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "type",
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   alt ],
             action =
               lam state9: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res9.
                   match
                     res9
                   with
                     [ LitParsed l7,
                       TokParsed (UIdentTok x6),
                       UserSym val2 ]
                   then
                     let val2: {__br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]} =
                       fromDyn
                         val2
                     in
                     asDyn
                       (TypeDeclOp
                          { __br_terms =
                              join
                                [ [ l7.info ],
                                  [ x6.info ],
                                  val2.__br_terms ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l7.info)
                                [ x6.info,
                                  val2.__br_info ],
                            name =
                              [ { v =
                                    nameNoSym
                                      (x6.val),
                                  i =
                                    x6.info } ],
                            properties =
                              val2.properties })
                   else
                     never },
           { nt =
               alt1,
             label =
               {},
             rhs =
               "",
             action =
               lam state10: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res10.
                   match
                     res10
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         name =
                           "" }
                   else
                     never },
           { nt =
               alt1,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}) ],
             action =
               lam state11: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res11.
                   match
                     res11
                   with
                     [ TokParsed (UIdentTok x7) ]
                   then
                     asDyn
                       { __br_terms =
                           [ x7.info ],
                         __br_info =
                           x7.info,
                         name =
                           [ { v =
                                 nameNoSym
                                   (x7.val),
                               i =
                                 x7.info } ] }
                   else
                     never },
           { nt =
               kleene2,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 litSym
                   ",",
                 ntSym
                   kleene2 ],
             action =
               lam state12: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res12.
                   match
                     res12
                   with
                     [ TokParsed (LIdentTok x8),
                       LitParsed l8,
                       UserSym ntVal3,
                       LitParsed l9,
                       UserSym val3 ]
                   then
                     let ntVal3: (Info, Expr) =
                       fromDyn
                         ntVal3
                     in
                     let val3: {__br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]} =
                       fromDyn
                         val3
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ x8.info ],
                               [ l8.info ],
                               [ l9.info ],
                               val3.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (x8.info)
                             [ l8.info,
                               ntVal3.#label"0",
                               l9.info,
                               val3.__br_info ],
                         properties =
                           concat
                             [ { val =
                                   match
                                     [ ntVal3.#label"1" ]
                                   with
                                     [ x9 ] ++ _ ++ ""
                                   then
                                     x9
                                   else
                                     never,
                                 name =
                                   match
                                     [ { v =
                                           x8.val,
                                         i =
                                           x8.info } ]
                                   with
                                     [ x10 ] ++ _ ++ ""
                                   then
                                     x10
                                   else
                                     never } ]
                             (val3.properties) }
                   else
                     never },
           { nt =
               kleene2,
             label =
               {},
             rhs =
               "",
             action =
               lam state13: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res13.
                   match
                     res13
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         properties =
                           "" }
                   else
                     never },
           { nt =
               alt2,
             label =
               {},
             rhs =
               "",
             action =
               lam state14: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res14.
                   match
                     res14
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         properties =
                           "" }
                   else
                     never },
           { nt =
               alt2,
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   kleene2,
                 litSym
                   "}" ],
             action =
               lam state15: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res15.
                   match
                     res15
                   with
                     [ LitParsed l10,
                       UserSym val3,
                       LitParsed l11 ]
                   then
                     let val3: {__br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]} =
                       fromDyn
                         val3
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ l10.info ],
                               val3.__br_terms,
                               [ l11.info ] ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l10.info)
                             [ val3.__br_info,
                               l11.info ],
                         properties =
                           val3.properties }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "token",
                 ntSym
                   alt1,
                 ntSym
                   alt2 ],
             action =
               lam state16: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res16.
                   match
                     res16
                   with
                     [ LitParsed l12,
                       UserSym val4,
                       UserSym val5 ]
                   then
                     let val4: {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val4
                     in
                     let val5: {__br_info: Info, __br_terms: [Info], properties: [{val: Expr, name: {i: Info, v: String}}]} =
                       fromDyn
                         val5
                     in
                     asDyn
                       (TokenDeclOp
                          { __br_terms =
                              join
                                [ [ l12.info ],
                                  val4.__br_terms,
                                  val5.__br_terms ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l12.info)
                                [ val4.__br_info,
                                  val5.__br_info ],
                            name =
                              val4.name,
                            properties =
                              val5.properties })
                   else
                     never },
           { nt =
               alt3,
             label =
               {},
             rhs =
               "",
             action =
               lam state17: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res17.
                   match
                     res17
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         noeq =
                           "" }
                   else
                     never },
           { nt =
               alt3,
             label =
               {},
             rhs =
               [ litSym
                   "~" ],
             action =
               lam state18: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res18.
                   match
                     res18
                   with
                     [ LitParsed l13 ]
                   then
                     asDyn
                       { __br_terms =
                           [ l13.info ],
                         __br_info =
                           l13.info,
                         noeq =
                           [ l13.info ] }
                   else
                     never },
           { nt =
               kleene3,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene3 ],
             action =
               lam state19: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res19.
                   match
                     res19
                   with
                     [ TokParsed (UIdentTok x11),
                       UserSym val6 ]
                   then
                     let val6: {__br_info: Info, operators: [{i: Info, v: Name}], __br_terms: [Info]} =
                       fromDyn
                         val6
                     in
                     asDyn
                       { __br_terms =
                           concat
                             [ x11.info ]
                             (val6.__br_terms),
                         __br_info =
                           mergeInfo
                             (x11.info)
                             (val6.__br_info),
                         operators =
                           concat
                             [ { v =
                                   nameNoSym
                                     (x11.val),
                                 i =
                                   x11.info } ]
                             (val6.operators) }
                   else
                     never },
           { nt =
               kleene3,
             label =
               {},
             rhs =
               "",
             action =
               lam state20: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res20.
                   match
                     res20
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         operators =
                           "" }
                   else
                     never },
           { nt =
               kleene4,
             label =
               {},
             rhs =
               [ ntSym
                   alt3,
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene3,
                 litSym
                   ";",
                 ntSym
                   kleene4 ],
             action =
               lam state21: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res21.
                   match
                     res21
                   with
                     [ UserSym val7,
                       TokParsed (UIdentTok x12),
                       UserSym val6,
                       LitParsed l14,
                       UserSym val8 ]
                   then
                     let val7: {noeq: [Info], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val7
                     in
                     let val6: {__br_info: Info, operators: [{i: Info, v: Name}], __br_terms: [Info]} =
                       fromDyn
                         val6
                     in
                     let val8: {levels: [{noeq: (Option) (Info), operators: [{i: Info, v: Name}]}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val8
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ val7.__br_terms,
                               [ x12.info ],
                               val6.__br_terms,
                               [ l14.info ],
                               val8.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (val7.__br_info)
                             [ x12.info,
                               val6.__br_info,
                               l14.info,
                               val8.__br_info ],
                         levels =
                           concat
                             [ { noeq =
                                   match
                                     val7.noeq
                                   with
                                     [ x13 ] ++ _ ++ ""
                                   then
                                     Some
                                       x13
                                   else
                                     None
                                       {},
                                 operators =
                                   concat
                                     [ { v =
                                           nameNoSym
                                             (x12.val),
                                         i =
                                           x12.info } ]
                                     (val6.operators) } ]
                             (val8.levels) }
                   else
                     never },
           { nt =
               kleene4,
             label =
               {},
             rhs =
               "",
             action =
               lam state22: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res22.
                   match
                     res22
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         levels =
                           "" }
                   else
                     never },
           { nt =
               kleene5,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene5 ],
             action =
               lam state23: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res23.
                   match
                     res23
                   with
                     [ TokParsed (UIdentTok x14),
                       UserSym val9 ]
                   then
                     let val9: {lefts: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val9
                     in
                     asDyn
                       { __br_terms =
                           concat
                             [ x14.info ]
                             (val9.__br_terms),
                         __br_info =
                           mergeInfo
                             (x14.info)
                             (val9.__br_info),
                         lefts =
                           concat
                             [ { v =
                                   nameNoSym
                                     (x14.val),
                                 i =
                                   x14.info } ]
                             (val9.lefts) }
                   else
                     never },
           { nt =
               kleene5,
             label =
               {},
             rhs =
               "",
             action =
               lam state24: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res24.
                   match
                     res24
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         lefts =
                           "" }
                   else
                     never },
           { nt =
               kleene6,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene6 ],
             action =
               lam state25: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res25.
                   match
                     res25
                   with
                     [ TokParsed (UIdentTok x15),
                       UserSym val10 ]
                   then
                     let val10: {rights: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val10
                     in
                     asDyn
                       { __br_terms =
                           concat
                             [ x15.info ]
                             (val10.__br_terms),
                         __br_info =
                           mergeInfo
                             (x15.info)
                             (val10.__br_info),
                         rights =
                           concat
                             [ { v =
                                   nameNoSym
                                     (x15.val),
                                 i =
                                   x15.info } ]
                             (val10.rights) }
                   else
                     never },
           { nt =
               kleene6,
             label =
               {},
             rhs =
               "",
             action =
               lam state26: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res26.
                   match
                     res26
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         rights =
                           "" }
                   else
                     never },
           { nt =
               kleene7,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene5,
                 litSym
                   "?",
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene6,
                 litSym
                   ";",
                 ntSym
                   kleene7 ],
             action =
               lam state27: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res27.
                   match
                     res27
                   with
                     [ TokParsed (UIdentTok x16),
                       UserSym val9,
                       LitParsed l15,
                       TokParsed (UIdentTok x17),
                       UserSym val10,
                       LitParsed l16,
                       UserSym val11 ]
                   then
                     let val9: {lefts: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val9
                     in
                     let val10: {rights: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val10
                     in
                     let val11: {__br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]} =
                       fromDyn
                         val11
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ x16.info ],
                               val9.__br_terms,
                               [ l15.info ],
                               [ x17.info ],
                               val10.__br_terms,
                               [ l16.info ],
                               val11.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (x16.info)
                             [ val9.__br_info,
                               l15.info,
                               x17.info,
                               val10.__br_info,
                               l16.info,
                               val11.__br_info ],
                         exceptions =
                           concat
                             [ { lefts =
                                   concat
                                     [ { v =
                                           nameNoSym
                                             (x16.val),
                                         i =
                                           x16.info } ]
                                     (val9.lefts),
                                 rights =
                                   concat
                                     [ { v =
                                           nameNoSym
                                             (x17.val),
                                         i =
                                           x17.info } ]
                                     (val10.rights) } ]
                             (val11.exceptions) }
                   else
                     never },
           { nt =
               kleene7,
             label =
               {},
             rhs =
               "",
             action =
               lam state28: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res28.
                   match
                     res28
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         exceptions =
                           "" }
                   else
                     never },
           { nt =
               alt4,
             label =
               {},
             rhs =
               "",
             action =
               lam state29: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res29.
                   match
                     res29
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         exceptions =
                           "" }
                   else
                     never },
           { nt =
               alt4,
             label =
               {},
             rhs =
               [ litSym
                   "except",
                 litSym
                   "{",
                 ntSym
                   kleene7,
                 litSym
                   "}" ],
             action =
               lam state30: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res30.
                   match
                     res30
                   with
                     [ LitParsed l17,
                       LitParsed l18,
                       UserSym val11,
                       LitParsed l19 ]
                   then
                     let val11: {__br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]} =
                       fromDyn
                         val11
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ l17.info ],
                               [ l18.info ],
                               val11.__br_terms,
                               [ l19.info ] ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l17.info)
                             [ l18.info,
                               val11.__br_info,
                               l19.info ],
                         exceptions =
                           val11.exceptions }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "precedence",
                 litSym
                   "{",
                 ntSym
                   kleene4,
                 litSym
                   "}",
                 ntSym
                   alt4 ],
             action =
               lam state31: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res31.
                   match
                     res31
                   with
                     [ LitParsed l20,
                       LitParsed l21,
                       UserSym val8,
                       LitParsed l22,
                       UserSym val12 ]
                   then
                     let val8: {levels: [{noeq: (Option) (Info), operators: [{i: Info, v: Name}]}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val8
                     in
                     let val12: {__br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]} =
                       fromDyn
                         val12
                     in
                     asDyn
                       (PrecedenceTableDeclOp
                          { __br_terms =
                              join
                                [ [ l20.info ],
                                  [ l21.info ],
                                  val8.__br_terms,
                                  [ l22.info ],
                                  val12.__br_terms ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l20.info)
                                [ l21.info,
                                  val8.__br_info,
                                  l22.info,
                                  val12.__br_info ],
                            levels =
                              val8.levels,
                            exceptions =
                              val12.exceptions })
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "prod" ],
             action =
               lam state32: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res32.
                   match
                     res32
                   with
                     [ LitParsed l23 ]
                   then
                     asDyn
                       { __br_terms =
                           [ l23.info ],
                         __br_info =
                           l23.info,
                         kinf =
                           "",
                         kpref =
                           "",
                         kprod =
                           [ l23.info ],
                         kpostf =
                           "" }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "infix" ],
             action =
               lam state33: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res33.
                   match
                     res33
                   with
                     [ LitParsed l24 ]
                   then
                     asDyn
                       { __br_terms =
                           [ l24.info ],
                         __br_info =
                           l24.info,
                         kinf =
                           [ l24.info ],
                         kpref =
                           "",
                         kprod =
                           "",
                         kpostf =
                           "" }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "prefix" ],
             action =
               lam state34: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res34.
                   match
                     res34
                   with
                     [ LitParsed l25 ]
                   then
                     asDyn
                       { __br_terms =
                           [ l25.info ],
                         __br_info =
                           l25.info,
                         kinf =
                           "",
                         kpref =
                           [ l25.info ],
                         kprod =
                           "",
                         kpostf =
                           "" }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "postfix" ],
             action =
               lam state35: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res35.
                   match
                     res35
                   with
                     [ LitParsed l26 ]
                   then
                     asDyn
                       { __br_terms =
                           [ l26.info ],
                         __br_info =
                           l26.info,
                         kinf =
                           "",
                         kpref =
                           "",
                         kprod =
                           "",
                         kpostf =
                           [ l26.info ] }
                   else
                     never },
           { nt =
               alt6,
             label =
               {},
             rhs =
               "",
             action =
               lam state36: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res36.
                   match
                     res36
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         assoc =
                           "" }
                   else
                     never },
           { nt =
               alt6,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}) ],
             action =
               lam state37: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res37.
                   match
                     res37
                   with
                     [ TokParsed (LIdentTok x18) ]
                   then
                     asDyn
                       { __br_terms =
                           [ x18.info ],
                         __br_info =
                           x18.info,
                         assoc =
                           [ { v =
                                 x18.val,
                               i =
                                 x18.info } ] }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ ntSym
                   alt5,
                 ntSym
                   alt6,
                 tokSym
                   (UIdentRepr
                      {}),
                 litSym
                   ":",
                 tokSym
                   (UIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Regex" ],
             action =
               lam state38: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res38.
                   match
                     res38
                   with
                     [ UserSym val13,
                       UserSym val14,
                       TokParsed (UIdentTok x19),
                       LitParsed l27,
                       TokParsed (UIdentTok x20),
                       LitParsed l28,
                       UserSym ntVal4 ]
                   then
                     let val13: {kinf: [Info], kpref: [Info], kprod: [Info], kpostf: [Info], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val13
                     in
                     let val14: {assoc: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val14
                     in
                     let ntVal4: (Info, Regex) =
                       fromDyn
                         ntVal4
                     in
                     asDyn
                       (ProductionDeclOp
                          { __br_terms =
                              join
                                [ val13.__br_terms,
                                  val14.__br_terms,
                                  [ x19.info ],
                                  [ l27.info ],
                                  [ x20.info ],
                                  [ l28.info ] ],
                            __br_info =
                              foldl
                                mergeInfo
                                (val13.__br_info)
                                [ val14.__br_info,
                                  x19.info,
                                  l27.info,
                                  x20.info,
                                  l28.info,
                                  ntVal4.#label"0" ],
                            nt =
                              [ { v =
                                    nameNoSym
                                      (x20.val),
                                  i =
                                    x20.info } ],
                            name =
                              [ { v =
                                    nameNoSym
                                      (x19.val),
                                  i =
                                    x19.info } ],
                            kinf =
                              val13.kinf,
                            kpref =
                              val13.kpref,
                            kprod =
                              val13.kprod,
                            kpostf =
                              val13.kpostf,
                            assoc =
                              val14.assoc,
                            regex =
                              [ ntVal4.#label"1" ] })
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   #var"Regex",
                 litSym
                   "}" ],
             action =
               lam state39: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res39.
                   match
                     res39
                   with
                     [ LitParsed l29,
                       UserSym ntVal5,
                       LitParsed l30 ]
                   then
                     let ntVal5: (Info, Regex) =
                       fromDyn
                         ntVal5
                     in
                     asDyn
                       (RecordRegexOp
                          { __br_terms =
                              concat
                                [ l29.info ]
                                [ l30.info ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l29.info)
                                [ ntVal5.#label"0",
                                  l30.info ],
                            regex =
                              [ ntVal5.#label"1" ] })
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ litSym
                   "empty" ],
             action =
               lam state40: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res40.
                   match
                     res40
                   with
                     [ LitParsed l31 ]
                   then
                     asDyn
                       (EmptyRegexOp
                          { __br_terms =
                              [ l31.info ],
                            __br_info =
                              l31.info })
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (StringRepr
                      {}) ],
             action =
               lam state41: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res41.
                   match
                     res41
                   with
                     [ TokParsed (StringTok x21) ]
                   then
                     asDyn
                       (LiteralRegexOp
                          { val =
                              [ { v =
                                    x21.val,
                                  i =
                                    x21.info } ],
                            __br_terms =
                              [ x21.info ],
                            __br_info =
                              x21.info })
                   else
                     never },
           { nt =
               alt7,
             label =
               {},
             rhs =
               "",
             action =
               lam state42: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res42.
                   match
                     res42
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         arg =
                           "" }
                   else
                     never },
           { nt =
               alt7,
             label =
               {},
             rhs =
               [ litSym
                   "[",
                 ntSym
                   #var"Expr",
                 litSym
                   "]" ],
             action =
               lam state43: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res43.
                   match
                     res43
                   with
                     [ LitParsed l32,
                       UserSym ntVal6,
                       LitParsed l33 ]
                   then
                     let ntVal6: (Info, Expr) =
                       fromDyn
                         ntVal6
                     in
                     asDyn
                       { __br_terms =
                           concat
                             [ l32.info ]
                             [ l33.info ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l32.info)
                             [ ntVal6.#label"0",
                               l33.info ],
                         arg =
                           [ ntVal6.#label"1" ] }
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   alt7 ],
             action =
               lam state44: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res44.
                   match
                     res44
                   with
                     [ TokParsed (UIdentTok x22),
                       UserSym val15 ]
                   then
                     let val15: {arg: [Expr], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val15
                     in
                     asDyn
                       (TokenRegexOp
                          { __br_terms =
                              concat
                                [ x22.info ]
                                (val15.__br_terms),
                            __br_info =
                              mergeInfo
                                (x22.info)
                                (val15.__br_info),
                            name =
                              [ { v =
                                    nameNoSym
                                      (x22.val),
                                  i =
                                    x22.info } ],
                            arg =
                              val15.arg })
                   else
                     never },
           { nt =
               #var"RegexPostfix",
             label =
               {},
             rhs =
               [ litSym
                   "+" ],
             action =
               lam state45: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res45.
                   match
                     res45
                   with
                     [ LitParsed l34 ]
                   then
                     asDyn
                       (RepeatPlusRegexOp
                          { __br_terms =
                              [ l34.info ],
                            __br_info =
                              l34.info })
                   else
                     never },
           { nt =
               #var"RegexPostfix",
             label =
               {},
             rhs =
               [ litSym
                   "*" ],
             action =
               lam state46: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res46.
                   match
                     res46
                   with
                     [ LitParsed l35 ]
                   then
                     asDyn
                       (RepeatStarRegexOp
                          { __br_terms =
                              [ l35.info ],
                            __br_info =
                              l35.info })
                   else
                     never },
           { nt =
               #var"RegexPostfix",
             label =
               {},
             rhs =
               [ litSym
                   "?" ],
             action =
               lam state47: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res47.
                   match
                     res47
                   with
                     [ LitParsed l36 ]
                   then
                     asDyn
                       (RepeatQuestionRegexOp
                          { __br_terms =
                              [ l36.info ],
                            __br_info =
                              l36.info })
                   else
                     never },
           { nt =
               #var"RegexPrefix",
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   ":" ],
             action =
               lam state48: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res48.
                   match
                     res48
                   with
                     [ TokParsed (LIdentTok x23),
                       LitParsed l37 ]
                   then
                     asDyn
                       (NamedRegexOp
                          { __br_terms =
                              concat
                                [ x23.info ]
                                [ l37.info ],
                            __br_info =
                              mergeInfo
                                (x23.info)
                                (l37.info),
                            name =
                              [ { v =
                                    x23.val,
                                  i =
                                    x23.info } ] })
                   else
                     never },
           { nt =
               #var"RegexInfix",
             label =
               {},
             rhs =
               [ litSym
                   "|" ],
             action =
               lam state49: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res49.
                   match
                     res49
                   with
                     [ LitParsed l38 ]
                   then
                     asDyn
                       (AlternativeRegexOp
                          { __br_terms =
                              [ l38.info ],
                            __br_info =
                              l38.info })
                   else
                     never },
           { nt =
               #var"RegexInfix",
             label =
               {},
             rhs =
               "",
             action =
               lam state50: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res50.
                   match
                     res50
                   with
                     ""
                   then
                     asDyn
                       (ConcatRegexOp
                          { __br_terms =
                              "",
                            __br_info =
                              NoInfo
                                {} })
                   else
                     never },
           { nt =
               #var"ExprInfix",
             label =
               {},
             rhs =
               "",
             action =
               lam state51: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res51.
                   match
                     res51
                   with
                     ""
                   then
                     asDyn
                       (AppExprOp
                          { __br_terms =
                              "",
                            __br_info =
                              NoInfo
                                {} })
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}) ],
             action =
               lam state52: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res52.
                   match
                     res52
                   with
                     [ TokParsed (UIdentTok x24) ]
                   then
                     asDyn
                       (ConExprOp
                          { __br_terms =
                              [ x24.info ],
                            __br_info =
                              x24.info,
                            name =
                              [ { v =
                                    nameNoSym
                                      (x24.val),
                                  i =
                                    x24.info } ] })
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (StringRepr
                      {}) ],
             action =
               lam state53: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res53.
                   match
                     res53
                   with
                     [ TokParsed (StringTok x25) ]
                   then
                     asDyn
                       (StringExprOp
                          { val =
                              [ { v =
                                    x25.val,
                                  i =
                                    x25.info } ],
                            __br_terms =
                              [ x25.info ],
                            __br_info =
                              x25.info })
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}) ],
             action =
               lam state54: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res54.
                   match
                     res54
                   with
                     [ TokParsed (LIdentTok x26) ]
                   then
                     asDyn
                       (VariableExprOp
                          { __br_terms =
                              [ x26.info ],
                            __br_info =
                              x26.info,
                            name =
                              [ { v =
                                    nameNoSym
                                      (x26.val),
                                  i =
                                    x26.info } ] })
                   else
                     never },
           { nt =
               kleene8,
             label =
               {},
             rhs =
               [ litSym
                   ",",
                 tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 ntSym
                   kleene8 ],
             action =
               lam state55: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res55.
                   match
                     res55
                   with
                     [ LitParsed l39,
                       TokParsed (LIdentTok x27),
                       LitParsed l40,
                       UserSym ntVal7,
                       UserSym val16 ]
                   then
                     let ntVal7: (Info, Expr) =
                       fromDyn
                         ntVal7
                     in
                     let val16: {fields: [{val: Expr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val16
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ l39.info ],
                               [ x27.info ],
                               [ l40.info ],
                               val16.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l39.info)
                             [ x27.info,
                               l40.info,
                               ntVal7.#label"0",
                               val16.__br_info ],
                         fields =
                           concat
                             [ { val =
                                   match
                                     [ ntVal7.#label"1" ]
                                   with
                                     [ x28 ] ++ _ ++ ""
                                   then
                                     x28
                                   else
                                     never,
                                 name =
                                   match
                                     [ { v =
                                           x27.val,
                                         i =
                                           x27.info } ]
                                   with
                                     [ x29 ] ++ _ ++ ""
                                   then
                                     x29
                                   else
                                     never } ]
                             (val16.fields) }
                   else
                     never },
           { nt =
               kleene8,
             label =
               {},
             rhs =
               "",
             action =
               lam state56: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res56.
                   match
                     res56
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         fields =
                           "" }
                   else
                     never },
           { nt =
               alt8,
             label =
               {},
             rhs =
               "",
             action =
               lam state57: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res57.
                   match
                     res57
                   with
                     ""
                   then
                     asDyn
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {},
                         fields =
                           "" }
                   else
                     never },
           { nt =
               alt8,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 ntSym
                   kleene8 ],
             action =
               lam state58: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res58.
                   match
                     res58
                   with
                     [ TokParsed (LIdentTok x30),
                       LitParsed l41,
                       UserSym ntVal8,
                       UserSym val16 ]
                   then
                     let ntVal8: (Info, Expr) =
                       fromDyn
                         ntVal8
                     in
                     let val16: {fields: [{val: Expr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val16
                     in
                     asDyn
                       { __br_terms =
                           join
                             [ [ x30.info ],
                               [ l41.info ],
                               val16.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (x30.info)
                             [ l41.info,
                               ntVal8.#label"0",
                               val16.__br_info ],
                         fields =
                           concat
                             [ { val =
                                   match
                                     [ ntVal8.#label"1" ]
                                   with
                                     [ x31 ] ++ _ ++ ""
                                   then
                                     x31
                                   else
                                     never,
                                 name =
                                   match
                                     [ { v =
                                           x30.val,
                                         i =
                                           x30.info } ]
                                   with
                                     [ x32 ] ++ _ ++ ""
                                   then
                                     x32
                                   else
                                     never } ]
                             (val16.fields) }
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   alt8,
                 litSym
                   "}" ],
             action =
               lam state59: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res59.
                   match
                     res59
                   with
                     [ LitParsed l42,
                       UserSym val17,
                       LitParsed l43 ]
                   then
                     let val17: {fields: [{val: Expr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} =
                       fromDyn
                         val17
                     in
                     asDyn
                       (RecordExprOp
                          { __br_terms =
                              join
                                [ [ l42.info ],
                                  val17.__br_terms,
                                  [ l43.info ] ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l42.info)
                                [ val17.__br_info,
                                  l43.info ],
                            fields =
                              val17.fields })
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ litSym
                   "(",
                 ntSym
                   #var"Regex",
                 litSym
                   ")" ],
             action =
               lam #var"".
                 lam seq.
                   match
                     seq
                   with
                     [ LitParsed l44,
                       UserSym ntVal9,
                       LitParsed l45 ]
                   then
                     let ntVal9: (Info, Regex) =
                       fromDyn
                         ntVal9
                     in
                     asDyn
                       (RegexGrouping
                          { __br_terms =
                              [ l44.info,
                                l45.info ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l44.info)
                                [ ntVal9.#label"0",
                                  l45.info ],
                            inner =
                              match
                                [ ntVal9.#label"1" ]
                              with
                                [ x33 ]
                              then
                                x33
                              else
                                never })
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ litSym
                   "(",
                 ntSym
                   #var"Expr",
                 litSym
                   ")" ],
             action =
               lam #var"".
                 lam seq1.
                   match
                     seq1
                   with
                     [ LitParsed l46,
                       UserSym ntVal10,
                       LitParsed l47 ]
                   then
                     let ntVal10: (Info, Expr) =
                       fromDyn
                         ntVal10
                     in
                     asDyn
                       (ExprGrouping
                          { __br_terms =
                              [ l46.info,
                                l47.info ],
                            __br_info =
                              foldl
                                mergeInfo
                                (l46.info)
                                [ ntVal10.#label"0",
                                  l47.info ],
                            inner =
                              match
                                [ ntVal10.#label"1" ]
                              with
                                [ x33 ]
                              then
                                x33
                              else
                                never })
                   else
                     never },
           { nt =
               #var"File",
             label =
               {},
             rhs =
               [ ntSym
                   #var"File_lclosed" ],
             action =
               lam #var"".
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym cont ]
                   then
                     fromDyn
                       cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"File_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FileAtom",
                 ntSym
                   #var"File_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addFileOpAtom
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"File_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FileInfix",
                 ntSym
                   #var"File_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addFileOpInfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"File_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FilePrefix",
                 ntSym
                   #var"File_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addFileOpPrefix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"File_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FilePostfix",
                 ntSym
                   #var"File_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addFileOpPostfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"File_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   asDyn
                     (lam st.
                        finalizeFileOp
                          p
                          st) },
           { nt =
               #var"Decl",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Decl_lclosed" ],
             action =
               lam #var"".
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym cont ]
                   then
                     fromDyn
                       cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"Decl_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclAtom",
                 ntSym
                   #var"Decl_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addDeclOpAtom
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Decl_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclInfix",
                 ntSym
                   #var"Decl_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addDeclOpInfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Decl_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclPrefix",
                 ntSym
                   #var"Decl_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addDeclOpPrefix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Decl_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclPostfix",
                 ntSym
                   #var"Decl_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addDeclOpPostfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Decl_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   asDyn
                     (lam st.
                        finalizeDeclOp
                          p
                          st) },
           { nt =
               #var"Regex",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Regex_lclosed" ],
             action =
               lam #var"".
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym cont ]
                   then
                     fromDyn
                       cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"Regex_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexAtom",
                 ntSym
                   #var"Regex_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addRegexOpAtom
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Regex_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexInfix",
                 ntSym
                   #var"Regex_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addRegexOpInfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Regex_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexPrefix",
                 ntSym
                   #var"Regex_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addRegexOpPrefix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Regex_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexPostfix",
                 ntSym
                   #var"Regex_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addRegexOpPostfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Regex_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   asDyn
                     (lam st.
                        finalizeRegexOp
                          p
                          st) },
           { nt =
               #var"Expr",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Expr_lclosed" ],
             action =
               lam #var"".
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym cont ]
                   then
                     fromDyn
                       cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"Expr_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprAtom",
                 ntSym
                   #var"Expr_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addExprOpAtom
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Expr_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprInfix",
                 ntSym
                   #var"Expr_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addExprOpInfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Expr_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprPrefix",
                 ntSym
                   #var"Expr_lclosed" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addExprOpPrefix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Expr_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprPostfix",
                 ntSym
                   #var"Expr_lopen" ],
             action =
               lam p.
                 lam seq2.
                   match
                     seq2
                   with
                     [ UserSym x33,
                       UserSym cont ]
                   then
                     asDyn
                       (lam st.
                          fromDyn
                            cont
                            (addExprOpPostfix
                               p
                               (fromDyn
                                  x33)
                               st))
                   else
                     never },
           { nt =
               #var"Expr_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   asDyn
                     (lam st.
                        finalizeExprOp
                          p
                          st) } ] })
in
match
  target
with
  Right table
then
  table
else
  never

let parseSelfhost
: String -> String -> Either [(Info, String)] File
= lam filename. lam content.
  use ParseSelfhost in
  let config = {errors = ref [], content = content} in
  let res = parseWithTable _table filename config content in
  switch (res, deref config.errors)
  case (Right dyn, []) then
    match fromDyn dyn with (_, res) in Right res
  case (Left err, errors) then
    let err = ll1DefaultHighlight content (ll1ToErrorHighlightSpec err) in
    Left (snoc errors err)
  case (_, errors) then
    Left errors
  end

let parseSelfhostExn
: String -> String -> File
= lam filename. lam content.
  switch parseSelfhost filename content
  case Left errors then
    for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
    exit 1
  case Right file then file
  end