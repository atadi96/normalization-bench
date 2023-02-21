
// su
// ulimit -s unlimited
// dotnet run -c Release

module MyProgram

open HOASNf
open HOASNf.CBN

let test () =
  let forceC = HOASNf.CBN.force
  let repetitions = 2L
  timed "Nat 5M conversion"      repetitions (fun _ -> conv0 n5M n5Mb)
  timed "Nat 5M normalization"   repetitions (fun _ -> force (quote0 n5M))
  timed "Nat 5M normalization cont"   repetitions (fun _ -> forceC (quoteC0 n5M))
  printfn ""; printfn ""
  timed "Nat 10M conversion"     repetitions (fun _ -> conv0 n10M n10Mb)
  timed "Nat 10M normalization"  repetitions (fun _ -> force (quote0 n10M))
  timed "Nat 10M normalization cont"  repetitions (fun _ -> forceC (quoteC0 n10M))
  printfn ""; printfn ""
  timed "Tree 2M conversion"     repetitions (fun _ -> conv0 (ap fullTree n20) (ap fullTree n20b))
  timed "Tree 2M normalization"  repetitions (fun _ -> force (quote0 (ap fullTree n20)))
  timed "Tree 2M normalization cont"  repetitions (fun _ -> forceC (quoteC0 (ap fullTree n20)))
  printfn ""; printfn ""
  timed "Tree 4M conversion"     repetitions (fun _ -> conv0 (ap fullTree n21) (ap fullTree n21b))
  timed "Tree 4M normalization"  repetitions (fun _ -> force (quote0 (ap fullTree n21)))
  timed "Tree 4M normalization cont"  repetitions (fun _ -> forceC (quoteC0 (ap fullTree n21)))
  printfn ""; printfn ""
  timed "Tree 8M conversion"     repetitions (fun _ -> conv0 (ap fullTree n22) (ap fullTree n22b))
  timed "Tree 8M normalization"  repetitions (fun _ -> force (quote0 (ap fullTree n22)))
  timed "Tree 8M normalization cont"  repetitions (fun _ -> forceC (quoteC0 (ap fullTree n22)))

open HOASNf

let test2 () =
    let f x = x |> IL.quote0 |> force
    timed "Expr 10k norm" 2 (fun _ -> f IL.n10k)
    timed "Expr 10k compile" 2 (fun _ -> IL.compile IL.n10k)
    let compiled = IL.compile IL.n10k
    timed "Expr 10k compiled" 2 (fun _ -> force (compiled ()))
    timed "Val 10k norm" 2 (fun _ -> force (quote0 n10k))

let test3 () =
    IL.n2
    |> IL.quote0
    |> printfn "%A"

    IL.n5
    |> IL.quote0
    |> printfn "%A"

    IL.n10
    |> IL.quote0
    |> printfn "%A"
    
let test5 () =
    ILClosure.n2
    |> ILClosure.quote0
    |> printfn "%A"
    
    ILClosure.n5
    |> ILClosure.quote0
    |> printfn "%A"
    
    ILClosure.n10
    |> ILClosure.quote0
    |> printfn "%A"

let test4 () =
    let repetitions = 2L
    timed "Nat 5M normalization cont"   repetitions (fun _ -> force (quoteC0 n5M))
    timed "IL 5M compilation" repetitions (fun _ -> IL.compile IL.n5M)
    let compiled = IL.compile IL.n5M
    timed "IL 5M compiled normalization" repetitions (fun _ -> force (compiled ()))

open HOASGraph

let test6 () =
    printfn "%A" (quote0 (ap n2 n2))

[<EntryPoint>]
let main argv =
    let thread = System.Threading.Thread(new System.Threading.ThreadStart(test6), System.Int32.MaxValue)
    thread.Start()
    thread.Join()

    0
