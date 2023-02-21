module HOASNf

open System.Diagnostics

  type Val = VVar of int | VApp of Val * Val | VLam of (Val -> Val)
  type Tm = Var of int | App of Tm * Tm | Lam of Tm

  let inline ap t u = match t with VLam f -> f u | t -> VApp(t, u)
  let inline ap2 t u v = ap (ap t u) v

  let n2  = VLam (fun s -> VLam (fun z -> ap s (ap s z)))
  let n5  = VLam (fun s -> VLam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))
  let mul = VLam (fun a -> VLam (fun b -> VLam (fun s -> VLam (fun z -> ap (ap a (ap b s)) z))))
  let suc n  = VLam (fun s -> VLam (fun z -> ap s (ap2 n s z)))
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

  let leaf = VLam(fun l -> VLam(fun n -> l))
  let node = VLam(fun t1 -> VLam(fun t2 -> VLam(fun l -> VLam(fun n ->
                  ap2 n t1 t2))))
  let fullTree = VLam(fun n -> ap2 n (VLam(fun t -> ap2 node t t)) leaf)

  let rec quote l v =
    match v with
      | VVar x      -> Var (l - x - 1)
      | VLam t      ->  Lam (quote (l + 1) (t (VVar(l))))
      | VApp (t, u) -> App (quote l t, quote l u)

  let rec quoteC (l:int) (v: Val) (cont: Tm -> 'a): 'a =
    match v with
    | VVar x -> cont (Var (l - x - 1))
    | VLam t -> quoteC (l + 1) (t (VVar l)) (fun tm -> cont (Lam tm))
    | VApp (t, u) -> quoteC l t (fun tTm ->
                     quoteC l u (fun uTm ->
                        cont (App (tTm, uTm))))

  let quote0 = quote 0

  let quoteC0 value = quoteC 0 value id

  let rec conv (d:int) l r =
      match (l, r) with
      | (VVar(x), VVar(y)) -> x = y
      | (VApp(l1, l2), VApp(r1, r2)) -> conv d l1 r1 && conv d l2 r2
      | (VLam(l), VLam(r)) -> conv (d + 1) (l(VVar(d))) (r(VVar(d)))
      | _ -> false

  let conv0 = conv 0

  let natToInt (t : Tm) : int =
    match t with
      | Lam (Lam t) ->
          let mutable acc = 0
          let mutable u = t
          let upd() =  match u with App(_, u') -> u <- u'; true
                                  | _          -> false
          while upd() do
            acc <- acc + 1
          acc
      | _ -> 1

  let force (t : Tm) =
    match t with Lam(_) -> true
               | _      -> false

  let timed (msg:string) (times: int64) (act: Unit -> 'a) =
        printfn "%s" msg
        eprintfn "  Iterations: %A" times
        let t = Stopwatch()
        t.Start()
        for i in 1L .. times do
          eprintf "  %A" (act ())
        t.Stop()
        printfn "\nAverage time: %A ms" (t.ElapsedMilliseconds / times)
        printfn ""

module Lazy =
    type TmL = VarL of int | AppL of TmL Lazy * TmL Lazy | LamL of TmL Lazy

    let (|VarL'|AppL'|LamL'|) = function
        | VarL i -> Choice1Of3 i
        | AppL (fl, xl) -> Choice2Of3 (fl.Force(), xl.Force())
        | LamL lam -> Choice3Of3 (lam.Force())
        
    let rec quote l v =
        match v with
        | VVar x      -> VarL (l - x - 1)
        | VLam t      ->  LamL <| lazy (quote (l + 1) (t (VVar(l))))
        | VApp (t, u) -> AppL (lazy (quote l t), lazy (quote l u))
        (*
    let rec quoteC (l:int) (v: Val) (cont: Tm -> 'a): 'a =
        match v with
        | VVar x -> cont (Var (l - x - 1))
        | VLam t -> quoteC (l + 1) (t (VVar l)) (fun tm -> cont (Lam tm))
        | VApp (t, u) -> quoteC l t (fun tTm ->
                            quoteC l u (fun uTm ->
                            cont (App (tTm, uTm))))
        *)
    let quote0 = quote 0
        
    //let quoteC0 value = quoteC 0 value id
        
    let rec conv (d:int) l r =
        match (l, r) with
        | (VVar(x), VVar(y)) -> x = y
        | (VApp(l1, l2), VApp(r1, r2)) -> conv d l1 r1 && conv d l2 r2
        | (VLam(l), VLam(r)) -> conv (d + 1) (l(VVar(d))) (r(VVar(d)))
        | _ -> false
        
    let conv0 = conv 0
        
    let natToInt (t : TmL) : int =
        match t with
        | LamL' (LamL' t) ->
            let mutable acc = 0
            let mutable u = t
            let upd() =  match u with AppL'(_, u') -> u <- u'; true
                                    | _          -> false
            while upd() do
                acc <- acc + 1
            acc
        | _ -> 1
        
    let rec force (t : TmL) =
        match t with
        | LamL' a -> force a
        | AppL' (f,x) -> force f && force x
        | VarL' _     -> true



module CBN =
  type Val = VVar of int | VApp of Val * Val Lazy | VLam of (Val Lazy -> Val Lazy)
  type Tm = Var of int | App of Tm * Tm | Lam of Tm
  
  let inline (!) (t: _ Lazy) = t.Force()
    
  let (|VVar'|VApp'|VLam'|) tm: Choice<_,_,Lazy<Val> -> Lazy<Val>> =
      match !tm with
      | VVar i -> VVar' i
      | VApp (f,x) -> VApp' (f,x)
      | VLam f -> VLam' f

  let inline ap t u =
    match t with
    | VLam' f -> f u
    | Lazy tm -> lazy (VApp(tm, u))

  let inline ap2 t u v = ap (ap t u) v

  let n2  = lazy (VLam (fun s -> lazy (VLam (fun z -> ap s ( (ap s z))))))
  let n5  = lazy (VLam (fun s -> lazy (VLam (fun z -> ap s (ap s (ap s (ap s (ap s z))))))))
  let mul = lazy (VLam (fun a -> lazy (VLam (fun b -> lazy (VLam (fun s -> lazy (VLam (fun z -> ap (ap a (ap b s)) z))))))))
  let suc n  = lazy (VLam (fun s -> lazy (VLam (fun z -> ap s (ap2 n s z)))))
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

  let leaf = lazy (VLam(fun l -> lazy (VLam(fun n -> l))))
  let node = lazy (VLam(fun t1 -> lazy (VLam(fun t2 -> lazy (VLam(fun l -> lazy (VLam(fun n ->
                  ap2 n t1 t2))))))))
  let fullTree = lazy (VLam(fun n -> ap2 n (lazy (VLam(fun t -> ap2 node t t))) leaf))

  let rec quote l (v: Val) =
    match v with
      | VVar x      -> Var (l - x - 1)
      | VLam t      ->  Lam (quote (l + 1) !(t (lazy(VVar(l)))))
      | VApp (t, u) -> App (quote l t, quote l !u)

  let rec quoteC (l:int) (v: Val) (cont: Tm -> 'a): 'a =
    match v with
    | VVar x -> cont (Var (l - x - 1))
    | VLam t -> quoteC (l + 1) !(t (lazy (VVar l))) (fun tm -> cont (Lam tm))
    | VApp (t, u) -> quoteC l t (fun tTm ->
                     quoteC l !u (fun uTm ->
                        cont (App (tTm, uTm))))

  let quote0 (Lazy value) = quote 0 value

  let quoteC0 (Lazy value) = quoteC 0 value id

  let rec conv (d:int) l r =
      match (l, r) with
      | (VVar'(x), VVar'(y)) -> x = y
      | (VApp'(l1, l2), VApp'(r1, r2)) -> conv d (lazy l1) (lazy r1) && conv d l2 r2
      | (VLam'(l), VLam'(r)) -> conv (d + 1) (l(lazy (VVar(d)))) (r(lazy(VVar(d))))
      | _ -> false

  let conv0 l r = conv 0 l r

  let natToInt (t : Tm) : int =
    match t with
      | Lam (Lam t) ->
          let mutable acc = 0
          let mutable u = t
          let upd() =  match u with App(_, u') -> u <- u'; true
                                  | _          -> false
          while upd() do
            acc <- acc + 1
          acc
      | _ -> 1

  let force (t : Tm) =
    match t with Lam(_) -> true
               | _      -> false