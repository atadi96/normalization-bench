module HOASGraph

[<ReferenceEquality>]
type Var = { v: int }
let mutable private asht = 0
let newVar () =
    asht <- asht + 1
    { v = asht - 1 }

type Val =
    | VVar of Var
    | VApp of Val * Val
    | VLam of Var * Val

type ValCtx = (Val * Var list)

let var v = VVar v
let vapp f x = VApp (f, x)
let vlam (f : Val -> Val) =
    let var = newVar()
    VLam (var, f (VVar var))

type Tm =
    | Var of int
    | App of Tm * Tm
    | Lam of Tm

type ApVal =
    | ApVar of Var
    | ApAps of (Var * ApVal) list * ApVal
    | ApLamUnbound of (Var * ApVal)
    
type CtxItem = CtxApp of (Val * Val) | CtxLam of Var * Val | CtxUnbound of int
    
let (|CtxVal|CtxUb|) = function
    | CtxApp (f,x) -> CtxVal (VApp (f,x))
    | CtxLam (x,f) -> CtxVal (VLam (x,f))
    | CtxUnbound l -> CtxUb l
    
type Ctx = { lookup: Var -> CtxItem }

module Ctx =
    let private appendItem (x: Var) (item: CtxItem) {lookup = lookup} =
        {
            lookup = fun v ->
                if x = v then
                    item
                else lookup v
        }
    
    let appendVal (x: Var) (v: Val) ({ lookup = lookup } as ctx) =
        match v with
        | VVar appendVar -> 
            let varVal = lookup appendVar
            ctx |> appendItem x varVal
        | VApp (af,ax) ->
            ctx |> appendItem x (CtxApp (af,ax))
        | VLam (lx,lb) ->
            ctx |> appendItem x (CtxLam (lx,lb))

    let appendVals (paramList: (Var * Val) list) ({ lookup = lookup }) =
        let paramList =
            paramList
            |> List.map (fun (vvar,vval) ->
                match vval with
                | VVar appendVar -> (vvar, lookup vvar)
                | VApp (af,ax) -> (vvar, CtxApp (af,ax))
                | VLam (lx,lb) -> (vvar, CtxLam (lx,lb))
            )
        let lookupList (v: Var) =
            paramList
            |> List.tryFind (fst >> (=) v)
            |> Option.map snd
        {
            lookup = fun v ->
                lookupList v
                |> Option.defaultWith (fun () -> lookup v)
        }
    
    let appendUnbound (x: Var) (l: int) ctx =
        ctx |> appendItem x (CtxUnbound l)
    
    let empty =
        {
            lookup = fun _ -> failwith ""
        }

let apVal (vval: Val) (ctx: Ctx) =
    let (|CtxApp|CtxLam|CtxUnbound|) (_ : Val): Choice<(Val * Val), (Var * Val), int> = failwith ""

    let rec vAps (vval: Val) (apList: Val list)=
        match vval with
        | CtxApp (af,ax) ->
            failwith ""
            vAps af (ax :: apList)
        | _ -> vLams vval apList []

    and vLams (vval: Val) (apList: Val list) (paramList: (Var * Val) list) =
        match (vval, apList) with
        | CtxLam (lx, lb), ax :: axs ->
            vLams lb axs ((lx,ax) :: paramList)
        | _ -> (vval, apList, paramList)

    let (core, apList, paramList) = vAps vval []
    let ctx' = ctx |> Ctx.appendVals paramList
    core, apList


type Ctx = CtxVal of Val | CtxUnbound of int

let rec quote l (ctx: Var -> Ctx) vval =
    let rec lookup f v =
        match ctx v with
        | CtxUnbound x -> Var (l - x - 1)
        | CtxVal (VVar v') -> lookup f v'
        | CtxVal ctxVal -> f ctxVal
    let append v' vval (ctx: Var -> Ctx) = fun v ->
        if v = v' then
            vval
        else ctx v
    match vval with
    | VVar v ->
        lookup (quote l ctx) v
    | VApp (VLam (v,f), x) ->
        let ctx' =
            ctx
            |> append v (CtxVal x)

        quote l ctx' f
    | VApp (VVar v,x) ->
        v |> lookup (fun ctxVal ->
            printfn "%A" ctxVal
            match ctxVal with
            | VLam (lamV,body) -> 
                let ctx' = ctx |> append lamV (CtxVal x)
                quote l ctx' body
            | _ -> quote l ctx ctxVal
            )
    | VApp (f,x) ->
        App (quote l ctx f, quote l ctx x)
    | VLam (x,body) ->
        let ctx' =
            ctx
            |> append x (CtxUnbound l)
        Lam (quote (l + 1) ctx' body)

let quote0 = quote 0 (fun _ -> failwith "empty context")


let ap = vapp
let ap2 f x y = ap (ap f x) y

type ApTm = ExpTm

let n2  = vlam (fun s -> vlam (fun z -> ap s (ap s z)))
let n5  = vlam (fun s -> vlam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))
let mul = vlam (fun a -> vlam (fun b -> vlam (fun s -> vlam (fun z -> ap (ap a (ap b s)) z))))
let suc n  = vlam (fun s -> vlam (fun z -> ap s (ap2 n s z)))
let n10    = ap2 mul n2 n5
let n10b   = ap2 mul n5 n2
let n20    = ap2 mul n2 n10
let n20b   = ap2 mul n2 n10b
let n21    = suc n20
let n21b   = suc n20b
let n22    = suc n21
let n22b   = suc n21b
let n100   = ap2 mul n10  n10
let n100b  = ap2 mul n10b n10b
let n10k   = ap2 mul n100 n100
let n10kb  = ap2 mul n100b n100b
let n100k  = ap2 mul n10k n10
let n100kb = ap2 mul n10k n10
let n1M    = ap2 mul n10k n100
let n1Mb   = ap2 mul n10kb n100b
let n2M    = ap2 mul n1M  n2
let n2Mb   = ap2 mul n1Mb n2
let n5M    = ap2 mul n1M  n5
let n5Mb   = ap2 mul n1Mb  n5
let n10M   = ap2 mul n1M  n10
let n10Mb  = ap2 mul n1Mb n10b

