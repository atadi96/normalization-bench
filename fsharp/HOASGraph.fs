module HOASGraph

let debugfn format =
    let print str =
        //eprintfn "%s"
        ()
    Printf.kprintf print format

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
    
type Ctx = { lookup: Var -> CtxItem }
and CtxItem = CtxApp of (Val * Val) | CtxLam of Var * Val | CtxUnbound of int

let (|CtxVal|CtxUb|) = function
    | CtxApp (f,x) -> CtxVal (VApp (f,x))
    | CtxLam (x,f) -> CtxVal (VLam (x,f))
    | CtxUnbound l -> CtxUb l

module Ctx =
    let private appendItem (x: Var) (item: CtxItem) {lookup = lookup} =
        debugfn "HEEE [ %A; %A ]" x item
        {
            lookup = fun v ->
                if x = v then
                    debugfn ":LOOK %A %A" v item
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
                | VVar appendVar -> (vvar, lookup appendVar)
                | VApp (af,ax) -> (vvar, CtxApp (af,ax))
                | VLam (lx,lb) -> (vvar, CtxLam (lx,lb))
            )
        let lookupList (v: Var) =
            paramList
            |> List.tryFind (fst >> (=) v)
            |> Option.map (fun x ->
                debugfn "::LOOK %A" x
                x
            )
            |> Option.map snd
        {
            lookup = fun v ->
                debugfn "AAAAA %A" v
                lookupList v
                |> Option.defaultWith (fun () -> lookup v)
        }
    
    let appendUnbound (x: Var) (l: int) ctx =
        ctx |> appendItem x (CtxUnbound l)
    
    let empty =
        {
            lookup = fun _ -> failwith ""
        }

    let (|LookApp|LookLam|LookUnbound|) (ctx: Ctx, vval: Val) =
        match vval with
        | VVar v ->
            match v |> ctx.lookup with
            | CtxApp (af,ax) -> LookApp (af,ax)
            | CtxLam (lx,lb) -> LookLam (lx,lb)
            | CtxUnbound l -> LookUnbound l
        | VApp (af,ax) -> LookApp (af,ax)
        | VLam (lx,lb) -> LookLam (lx,lb)
        
        

let rec apVal (vval: Val) (ctx: Ctx) =
    debugfn "apVal"
    let (|LookApp|LookLam|LookUnbound|) (v : Val) =
        match (ctx,v) with
        | Ctx.LookApp (af,ax) -> LookApp (af,ax)
        | Ctx.LookLam (lx,lb) -> LookLam (lx,lb)
        | Ctx.LookUnbound l -> LookUnbound l

    let rec vAps (vval: Val) (apList: Val list)=
        debugfn "vAps"
        match vval with
        | LookApp (af,ax) ->
            debugfn "vAps LookApp [ %A; %A ]" af ax
            vAps af (ax :: apList)
        | _ -> vLams vval apList []

    and vLams (vval: Val) (apList: Val list) (paramList: (Var * Val) list) =
        debugfn "vLams"
        match (vval, apList) with
        | LookLam (lx, lb), ax :: axs ->
            vLams lb axs ((lx,ax) :: paramList)
        | _ -> (vval, apList, paramList)

    let (core, apList, paramList) = vAps vval []
    debugfn "apVal: %A <> %A <> %A" core apList paramList
    match paramList with
    | [] ->
        Error (core, apList)
    | _ ->
        let ctx' = ctx |> Ctx.appendVals paramList
        Ok (core, apList, ctx')


let rec quote l (ctx: Ctx) vval =
    debugfn "QUOTE %A" vval
    let (|DeepAps|UnboundAps|LookApp|LookLam|LookUnbound|) (v : Val) =
        match apVal v ctx with
        | Ok (core, apList, ctx') -> 
            DeepAps (core,apList,ctx')
        | Error (_, []) ->
            match (ctx,v) with
            | Ctx.LookApp x -> LookApp x
            | Ctx.LookLam x -> LookLam x
            | Ctx.LookUnbound x -> LookUnbound x
        | Error (core, apList) -> UnboundAps (core, apList)

    match vval with
    | LookLam (lx,lb) ->
        let ctx' = ctx |> Ctx.appendUnbound lx l
        Lam (quote (l + 1) ctx' lb)
    | LookApp (af,ax) ->
        App (quote l ctx af, quote l ctx ax)
    | LookUnbound x ->
        Var (l - x - 1)
    | DeepAps (core, apList, ctx') ->
        let reApp =
            apList
            |> List.fold (fun af ax -> VApp(af,ax)) core
        quote l ctx' reApp
    | UnboundAps (core, apList) ->
        apList
        |> List.map (quote l ctx)
        |> List.fold (fun af ax -> App (af,ax)) (quote l ctx core)

let quote0 = quote 0 Ctx.empty


let ap = vapp
let ap2 f x y = ap (ap f x) y
let let' x f = vapp (vlam f) x

type ApTm = ExpTm

let n2  = vlam (fun s -> vlam (fun z -> ap s (ap s z)))
let n5  = vlam (fun s -> vlam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))
let mul = vlam (fun a -> vlam (fun b -> vlam (fun s -> vlam (fun z -> ap (ap a (ap b s)) z))))
let n4 = let' n2 (fun n2 -> ap2 mul n2 n2)
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

