module Generics


type Val<'t> = VVar of 't | VApp of Val<'t> * Val<'t> | VLam of ('t -> Val<'t>)

type Tm = Var of int | App of Tm * Tm | Lam of Tm

let rec quote<'t when 't: equality> (freshVariable: unit -> 't) (l: 't -> int) (v: Val<'t>): Tm =
    match v with
    | VVar t -> Var (l t)
    | VApp (vf, vx) -> App (quote freshVariable l vf, quote freshVariable l vx)
    | VLam vf ->
        let variable = freshVariable()
        let l x =
            if x = variable then
                0
            else l x + 1
        quote freshVariable l (vf variable)

module Examples =
    let inline ap<'a> (t: Val<'a>) u =
        match t, u with
        | VLam f, VVar x -> f x
        | _ -> VApp(t, u)
    let inline ap2<'t> (t: Val<'t>) u v = ap (ap t u) v

    let n2  = VLam (fun s -> VLam (fun z -> ap (VVar s) (ap (VVar s) (VVar z))))
    let n5  = VLam (fun s -> VLam (fun z -> ap (VVar s) (ap (VVar s) (ap (VVar s) (ap (VVar s) (ap (VVar s) (VVar z)))))))
    let mul = VLam (fun a -> VLam (fun b -> VLam (fun s -> VLam (fun z -> ap (ap (VVar a) (ap (VVar b) (VVar s))) (VVar z)))))
    let suc<'a> n  = VLam (fun s -> VLam (fun z -> ap<'a> (VVar s) (ap2<'a> n (VVar s) (VVar z))))
    let n10<'a>    = ap2<'a> mul n2 n5
    let n10b<'a>   = ap2<'a> mul n5 n2
    let n20<'a>    = ap2<'a> mul n2 n10
    let n20b<'a>   = ap2<'a> mul n2 n10b
    let n21<'a>    = suc<'a> n20
    let n21b<'a>   = suc<'a> n20b
    let n22<'a>    = suc<'a> n21
    let n22b<'a>   = suc<'a> n21b
    let n100<'a>   = ap2<'a> mul n10  n10
    let n100b<'a>  = ap2<'a> mul n10b n10b
    let n10k<'a>   = ap2<'a> mul n100 n100
    let n10kb<'a>  = ap2<'a> mul n100b n100b
    let n100k<'a>  = ap2<'a> mul n10k n10
    let n100kb<'a> = ap2<'a> mul n10k n10
    let n1M<'a>    = ap2<'a> mul n10k n100
    let n1Mb<'a>   = ap2<'a> mul n10kb n100b
    let n2M<'a>    = ap2<'a> mul n1M  n2
    let n2Mb<'a>   = ap2<'a> mul n1Mb n2
    let n5M<'a>    = ap2<'a> mul n1M  n5
    let n5Mb<'a>   = ap2<'a> mul n1Mb  n5
    let n10M<'a>   = ap2<'a> mul n1M  n10
    let n10Mb<'a>  = ap2<'a> mul n1Mb n10b

    let leaf = VLam(fun l -> VLam(fun n -> VVar l))
    let node = VLam(fun t1 -> VLam(fun t2 -> VLam(fun l -> VLam(fun n ->
                    ap2 (VVar n) (VVar t1) (VVar t2)))))
    let fullTree = VLam(fun n -> ap2 (VVar n) (VLam(fun t -> ap2 node (VVar t) (VVar t))) leaf)
        