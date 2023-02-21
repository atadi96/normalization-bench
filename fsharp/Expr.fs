module Expr

open System.Linq.Expressions

module Val =
    
    type Helper() =
        static member Var i = HOASNf.Var i
        static member App (f, x) = HOASNf.App (f,x)
        static member Lam t = HOASNf.Lam(t)

    type ToTm = int -> HOASNf.Tm

    let var i: ToTm = fun l -> HOASNf.Var (l - i - 1)
    let app (a: ToTm) (p: ToTm) : ToTm = fun l -> HOASNf.App (a l, p l)
    let lam (f: ToTm -> ToTm): ToTm = fun l -> f (var l) (l + 1)

    type ParameterExpression = Expression

    type ExpTm = ParameterExpression -> Expression

    let vvar (i: ParameterExpression): ExpTm = fun (l: ParameterExpression) ->
        let index = Expression.Subtract(Expression.Subtract(l, i), Expression.Constant(1))
        let body = Expression.Call(typeof<Helper>.GetMethod(nameof(Helper.Var)), index)
        body

    let vapp (a: ExpTm) (b: ExpTm): ExpTm = fun (l: ParameterExpression) ->
        let a' = a l
        let b' = b l
        let body = Expression.Call(typeof<Helper>.GetMethod(nameof(Helper.App)), a', b')
        body

    let vlam (f: ParameterExpression -> ExpTm): ExpTm = fun (l: ParameterExpression) ->
        let l' = Expression.Variable(typeof<int>)
        let assign = Expression.Assign(l', Expression.Add(l, Expression.Constant(1)))
        let lambdaBody = f l l'
        let body = Expression.Call(typeof<Helper>.GetMethod(nameof(Helper.Lam)), lambdaBody)
        Expression.Block(typeof<HOASNf.Tm>, [|l'|], assign, body)


    let example: ExpTm = vlam (fun s -> vlam (fun z -> vvar s))

    let fromHoas (hoas: HOASNf.Val) =
        let rec innerFromHoas (ctx: ParameterExpression list) (hoas: HOASNf.Val) =
            match hoas with
            | HOASNf.VVar i -> vvar ctx.[ctx.Length - i - 1]
            | HOASNf.VApp (f,x) -> vapp (innerFromHoas ctx f) (innerFromHoas ctx x)
            | HOASNf.VLam f -> vlam (fun s -> innerFromHoas (s::ctx) (f (HOASNf.VVar ctx.Length)))
        innerFromHoas [] hoas

    let compile (onConverted: unit -> unit) (onCompiled: unit -> unit) (exp: ExpTm) =
        let l = Expression.Variable(typeof<int>)
        let expEvaluated = exp l
        onConverted ()

        let lambda =
            Expression.Lambda<System.Func<HOASNf.Tm>>(
                Expression.Block(
                    typeof<HOASNf.Tm>,
                    [|l|],
                    Expression.Assign(l, Expression.Constant(0)),
                    expEvaluated
                )
            )

        let compiled = lambda.Compile(false)
        onCompiled ()
        fun () -> compiled.Invoke()

    module Ap =

        type ApCtx = ApCtx of ApTm list

        and ApTm = ApCtx -> ExpTm
        
        let vvar (i: ParameterExpression): ApTm = fun (ApCtx apCtx) ->
            List.fold vapp (vvar i) (apCtx |> List.map (fun apTm -> apTm (ApCtx [])))
        
        let vapp (a: ApTm) (b: ApTm): ApTm = fun (ApCtx apCtx) ->
            a (ApCtx (b :: apCtx))
        
        let vlam (f: ApTm -> ApTm): ApTm = fun (ApCtx apCtx) ->
            match apCtx with
            | [] -> vlam (fun x -> f (vvar x) (ApCtx []))
            | x :: xs -> f x (ApCtx xs)

        let ap (f: ApTm) (x: ApTm) : ApTm  = vapp f x
        
        let ap2 f x y = ap (ap f x) y

        let unAp (tm: ApTm): ExpTm = tm (ApCtx [])
        (*
        let n2  = vlam (fun s -> vlam (fun z -> ap (vvar s) (ap (vvar s) (vvar z))))
        let n5  = vlam (fun s -> vlam (fun z -> ap (vvar s) (ap (vvar s) (ap (vvar s) (ap (vvar s) (ap (vvar s) (vvar z)))))))
        let mul: ApTm = vlam (fun a -> vlam (fun b -> vlam (fun s -> vlam (fun z -> ap (ap (vvar a) (ap (vvar b) (vvar s))) (vvar z)))))
        let suc n: ApTm  = vlam (fun s -> vlam (fun z -> ap (vvar s) (ap2 n (vvar s) (vvar z)))) 

        ap2 mul n2 n5 =
        vapp (vapp (mul n2)) n5 =
        (vapp mul n2) (n5 [] :: [])
        
        *)
        let n2  = vlam (fun s -> vlam (fun z -> ap s (ap s z)))
        let n5  = vlam (fun s -> vlam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))
        let mul: ApTm = vlam (fun a -> vlam (fun b -> vlam (fun s -> vlam (fun z -> ap (ap a (ap b s)) z))))
        let suc n: ApTm  = vlam (fun s -> vlam (fun z -> ap s (ap2 n s z)))
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

    let unAp a: ExpTm = Ap.unAp a

    let n2: ExpTm  = unAp Ap.n2
    let n5: ExpTm  = unAp Ap.n5
    let n10: ExpTm    = unAp Ap.n10
    let n10b: ExpTm   = unAp Ap.n10b
    let n20: ExpTm    = unAp Ap.n20
    let n20b: ExpTm   = unAp Ap.n20b
    let n21: ExpTm    = unAp Ap.n21
    let n21b: ExpTm   = unAp Ap.n21b
    let n22: ExpTm    = unAp Ap.n22
    let n22b: ExpTm   = unAp Ap.n22b
    let n100: ExpTm   = unAp Ap.n100
    let n100b: ExpTm  = unAp Ap.n100b
    let n10k: ExpTm   = unAp Ap.n10k
    let n10kb: ExpTm  = unAp Ap.n10kb
    let n100k: ExpTm  = unAp Ap.n100k
    let n100kb: ExpTm = unAp Ap.n100kb
    let n1M: ExpTm    = unAp Ap.n1M
    let n1Mb: ExpTm   = unAp Ap.n1Mb
    let n2M: ExpTm    = unAp Ap.n2M
    let n2Mb: ExpTm   = unAp Ap.n2Mb
    let n5M: ExpTm    = unAp Ap.n5M
    let n5Mb: ExpTm   = unAp Ap.n5Mb
    let n10M: ExpTm   = unAp Ap.n10M
    let n10Mb: ExpTm  = unAp Ap.n10Mb

    let quote0 v = compile ignore ignore v ()