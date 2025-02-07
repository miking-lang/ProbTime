include "../argparse.mc"
include "ast.mc"

include "mexpr/ast.mc"
include "mexpr/lamlift.mc"

lang ProbTimeCodegenBase = MExprAst + MExprLambdaLift + ProbTimeAst
  type PTCompileEnv = {
    ast : Expr,
    llSolutions : Map Name LambdaLiftSolution,
    aliases : Map Name PTType,
    consts : Map Name PTExpr,
    topVarEnv : Map String Name,
    templates : Map Name {inputs : [PTPortDecl], outputs : [PTPortDecl]},
    options : RtpplOptions
  }

  sem emptyPTCompileEnv : RtpplOptions -> PTCompileEnv
  sem emptyPTCompileEnv =
  | options ->
    { ast = unit_, llSolutions = mapEmpty nameCmp, aliases = mapEmpty nameCmp
    , consts = mapEmpty nameCmp, topVarEnv = mapEmpty cmpString
    , templates = mapEmpty nameCmp, options = options }

  type CompileResult = Map Name Expr

  -- Recursively set the info field of all subexpressions of a given expression
  -- to the provided info value, while avoiding to overwrite existing info
  -- fields. This function also recurses down into type fields and patterns.
  sem withInfoRec : Info -> Expr -> Expr
  sem withInfoRec info =
  | e ->
    let e =
      match infoTm e with NoInfo _ then withInfo info e
      else e
    in
    let e = smap_Expr_Pat (withInfoRecPat info) e in
    let e = smap_Expr_Type (withInfoRecTy info) e in
    smap_Expr_Expr (withInfoRec info) e

  sem withInfoRecTy : Info -> Type -> Type
  sem withInfoRecTy info =
  | ty ->
    let ty =
      match infoTy ty with NoInfo _ then tyWithInfo info ty
      else ty
    in
    smap_Type_Type (withInfoRecTy info) ty

  sem withInfoRecPat : Info -> Pat -> Pat
  sem withInfoRecPat info =
  | p ->
    let p =
      match infoPat p with NoInfo _ then withInfoPat info p
      else p
    in
    let p = smap_Pat_Expr (withInfoRec info) p in
    let p = smap_Pat_Type (withInfoRecTy info) p in
    smap_Pat_Pat (withInfoRecPat info) p

  sem resolveTypeAlias : Map Name PTType -> PTType -> PTType
  sem resolveTypeAlias aliases =
  | ty & PTTAlias {id = id, args = args} ->
    if null args then
      match mapLookup id aliases with Some ty then resolveTypeAlias aliases ty
      else ty
    else ty
  | ty -> smapPTTypePTType (resolveTypeAlias aliases) ty
end
