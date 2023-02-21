module ILClosure

open System.Linq.Expressions

type Helper() =
    static member Var i = HOASNf.Var i
    static member App (f, x) = HOASNf.App (f,x)
    static member Lam t = HOASNf.Lam(t)

type ToTm = int -> HOASNf.Tm

let var i: ToTm = fun l -> HOASNf.Var (l - i - 1)
let app (a: ToTm) (p: ToTm) : ToTm = fun l -> HOASNf.App (a l, p l)
let lam (f: ToTm -> ToTm): ToTm = fun l -> f (var l) (l + 1)

type ExpTm = int -> Expression

let tmTy = typeof<HOASNf.Tm>

let wrapParam (nullExpression: Expression) (appExpression: ParameterExpression -> Expression) =
    let param = Expression.Parameter(tmTy)
    let cond = Expression.Condition(Expression.TypeIs(param, tmTy), appExpression param, nullExpression)
    Expression.Lambda(cond, param)

let vvar (i: int): ExpTm = fun (l: int) ->
    let index = Expression.Constant(l - i - 1)
    let var = Expression.Call(typeof<Helper>.GetMethod(nameof(Helper.Var)), index)
    let app (param: ParameterExpression): Expression = Expression.Call(typeof<Helper>.GetMethod(nameof(Helper.App)), var, param)
    wrapParam var app

let vapp (a: ExpTm) (b: ExpTm): ExpTm = fun (l: int) ->
    let a' = a l
    let b' = b l
    let app = Expression.Invoke(a', b')
    wrapParam app (fun param -> Expression.Invoke(app, param))

let vlam (f: ExpTm -> ExpTm): ExpTm = fun (l: int) ->
    let l' = l + 1
    let lambdaBody param = f param l'
    let lam = Expression.Call(typeof<Helper>.GetMethod(nameof(Helper.Lam)), lambdaBody (vvar l))
    wrapParam lam (fun param -> f (fun _ -> param) l')

let compile (tm: ExpTm) =
    let func = Expression.Lambda<System.Func<HOASNf.Tm, HOASNf.Tm>>(tm 0).Compile()
    fun () -> func.Invoke(Unchecked.defaultof<HOASNf.Tm>)

let quote0 tm = compile tm ()

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
let n22: ApTm    = suc n21
let n22b: ApTm   = suc n21b
let n100   = ap2 mul n10  n10
let n100b  = ap2 mul n10b n10b
let n10k   = ap2 mul n100 n100
let n10kb  = ap2 mul n100b n100b
let n100k: ApTm  = ap2 mul n10k n10
let n100kb: ApTm = ap2 mul n10k n10
let n1M    = ap2 mul n10k n100
let n1Mb   = ap2 mul n10kb n100b
let n2M: ApTm    = ap2 mul n1M  n2
let n2Mb: ApTm   = ap2 mul n1Mb n2
let n5M: ApTm    = ap2 mul n1M  n5
let n5Mb: ApTm   = ap2 mul n1Mb  n5
let n10M: ApTm   = ap2 mul n1M  n10
let n10Mb: ApTm  = ap2 mul n1Mb n10b

module ShallowFunctions =
    
    // val -> ap declosurize closurize -> declosurize = compile = Tm -> Tm minden -> run without gen0 collection
    // let n5  = vlam (fun s -> vlam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))
    (*
    let n5  = vlam (fun s -> vlam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))

    *)

    type Closurized<'T> =
        | Object of 'T
        | Closure of 'T * ('T -> 'T)

    type IVal<'T> =
        abstract member VVar: int -> 'T
        abstract member VApp: 'T -> 'T -> 'T
        abstract member VLam: ('T -> 'T) -> 'T

    type ApCtx<'T> = ApCtx of ApTm<'T> list
    and ApTm<'T> = ApCtx<'T> -> 'T

    type Ap<'T>(v: IVal<'T>) =
        interface IVal<ApTm<'T>> with
            member this.VApp(a: ApTm<'T>) (b: ApTm<'T>): ApTm<'T> = fun (ApCtx apCtx) ->
                a (ApCtx (b :: apCtx))

            member __.VVar(i: int): ApTm<'T> = fun (ApCtx apCtx) ->
                List.fold v.VApp (v.VVar i) (apCtx |> List.map (fun apTm -> apTm (ApCtx [])))

            member this.VLam(f: ApTm<'T> -> ApTm<'T>): ApTm<'T> = fun (ApCtx apCtx) ->
                match apCtx with
                | [] -> v.VLam (fun x -> f (fun _ -> x) (ApCtx []))
                | x :: xs -> f x (ApCtx xs)
                
    type Side = | Left | Right

    type ApClCtx<'T> = ApClCtx of ApClTm<'T> list
    and ApClTm<'T> = Side -> ApClCtx<'T> -> 'T

    type ApCl<'T>(v: IVal<'T>) =
        let forgetClosure (cl: Closurized<'T>) = failwith<'T> ""

        interface IVal<ApClTm<'T>> with
            member this.VApp(a: ApClTm<'T>) (b: ApClTm<'T>): ApClTm<'T> = fun side (ApClCtx apCtx) ->
                a Left (ApClCtx (b :: apCtx))

            member __.VVar(i: int): ApClTm<'T> = fun _side (ApClCtx apCtx) ->
                List.fold v.VApp (v.VVar i) (apCtx |> List.map (fun apTm -> apTm Right (ApClCtx [])))

            member this.VLam(f: ApClTm<'T> -> ApClTm<'T>): ApClTm<'T> = (*
                fun (ApClCtx apCtx) ->
                    match apCtx with
                    | [] -> v.VLam (fun x -> f (fun _ -> x) (ApClCtx []))
                    | x :: xs -> f x (ApClCtx xs)
                    *)
                failwith ""
