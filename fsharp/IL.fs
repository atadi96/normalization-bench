module IL

type Helper() =
    static member Var i = HOASNf.Var i
    static member App (f, x) = HOASNf.App (f,x)
    static member Lam t = HOASNf.Lam(t)

open System.Reflection.Emit
open System.Reflection

type Generator = ILGenerator -> unit
type GeneratorTm = LocalBuilder -> Generator

let vvar (i: LocalBuilder): GeneratorTm = fun l -> fun generator ->
    generator.Emit(OpCodes.Ldloc, l)
    generator.Emit(OpCodes.Ldloc, i)
    generator.Emit OpCodes.Sub
    generator.Emit OpCodes.Ldc_I4_1
    generator.Emit OpCodes.Sub

    generator.Emit(OpCodes.Call, typeof<Helper>.GetMethod(nameof(Helper.Var)))

let vapp (a: GeneratorTm) (b: GeneratorTm): GeneratorTm = fun l -> fun generator ->
    a l generator
    b l generator
    generator.Emit(OpCodes.Call, typeof<Helper>.GetMethod(nameof(Helper.App)))

let vlam (f: LocalBuilder -> GeneratorTm): GeneratorTm = fun l -> fun generator ->
    let l' = generator.DeclareLocal(typeof<int>)
    generator.Emit(OpCodes.Ldloc, l)
    generator.Emit OpCodes.Ldc_I4_1
    generator.Emit OpCodes.Add
    generator.Emit(OpCodes.Stloc, l')
    f l l' generator
    generator.Emit(OpCodes.Call, typeof<Helper>.GetMethod(nameof(Helper.Lam)))

(*

var hashCode = new Random().Next();
var asmName = new AssemblyName($"{typeof(Konbanwa).Name}asm{hashCode}");
var typeName = $"{typeof(Konbanwa).Name}{hashCode}";
var asmBuilder = AssemblyBuilder.DefineDynamicAssembly(asmName, AssemblyBuilderAccess.Run);
var moduleBuilder = asmBuilder.DefineDynamicModule(typeName);
var typeBuilder = moduleBuilder.DefineType(typeName, TypeAttributes.Public);
var methodBuilder = typeBuilder.DefineMethod("Run", MethodAttributes.Static, typeof(void), new [] { typeof(object[]) });

var ilGenerator = methodBuilder.GetILGenerator();

init(ilGenerator);
stmts(ilGenerator);

var createdType = typeBuilder.CreateType();

new Lokad.ILPack.AssemblyGenerator().GenerateAssembly(asmBuilder, "C:\\Users\\abonyi\\Desktop\\testasm.dll");

var runMethodInfo = createdType.GetMethods(BindingFlags.NonPublic | BindingFlags.Static)[0];

var run = (Action<object[]>)Delegate.CreateDelegate(typeof(Action<object[]>), runMethodInfo);
return () => run(_parameters);
*)

let compile (valTm: GeneratorTm): unit -> HOASNf.Tm =
    let init: ILGenerator -> LocalBuilder = fun il ->
        let l = il.DeclareLocal(typeof<int>)
        il.Emit OpCodes.Ldc_I4_0
        il.Emit(OpCodes.Stloc, l)
        l


    let hashCode = (new System.Random()).Next()
    let asmName = new System.Reflection.AssemblyName($"{typeof<Helper>.Name}asm{hashCode}");
    let typeName = $"{typeof<Helper>.Name}{hashCode}";
    let asmBuilder = AssemblyBuilder.DefineDynamicAssembly(asmName, AssemblyBuilderAccess.Run);
    let moduleBuilder = asmBuilder.DefineDynamicModule(typeName);
    let typeBuilder = moduleBuilder.DefineType(typeName, TypeAttributes.Public);
    let methodBuilder = typeBuilder.DefineMethod("Run", MethodAttributes.Static, typeof<HOASNf.Tm>, [||]);
    
    let ilGenerator = methodBuilder.GetILGenerator();
    
    let l = init(ilGenerator)

    valTm l ilGenerator

    ilGenerator.Emit OpCodes.Ret 
    
    let createdType = typeBuilder.CreateType();
    
    (new Lokad.ILPack.AssemblyGenerator()).GenerateAssembly(asmBuilder, "C:\\Users\\atadi\\Desktop\\testasm2.dll");
    
    let runMethodInfo = createdType.GetMethods(BindingFlags.NonPublic ||| BindingFlags.Static)[0];
    
    let run = System.Delegate.CreateDelegate(typeof<System.Func<HOASNf.Tm>>, runMethodInfo) :?> System.Func<HOASNf.Tm>
    fun () -> run.Invoke()

let quote0 tm = compile tm ()
    
module Ap =
    
    type ApCtx = ApCtx of ApTm list
    
    and ApTm = ApCtx -> GeneratorTm
            
    let vvar (i: LocalBuilder): ApTm = fun (ApCtx apCtx) ->
        List.fold vapp (vvar i) (apCtx |> List.map (fun apTm -> apTm (ApCtx [])))
            
    let vapp (a: ApTm) (b: ApTm): ApTm = fun (ApCtx apCtx) ->
        a (ApCtx (b :: apCtx))
            
    let vlam (f: ApTm -> ApTm): ApTm = fun (ApCtx apCtx) ->
        match apCtx with
        | [] -> vlam (fun x -> f (vvar x) (ApCtx []))
        | x :: xs -> f x (ApCtx xs)
    
    let ap (f: ApTm) (x: ApTm) : ApTm  = vapp f x
            
    let ap2 f x y = ap (ap f x) y
    
    let unAp (tm: ApTm): GeneratorTm = tm (ApCtx [])
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
    
let unAp a: GeneratorTm = Ap.unAp a
    
let n2: GeneratorTm  = unAp Ap.n2
let n5: GeneratorTm  = unAp Ap.n5
let n10: GeneratorTm    = unAp Ap.n10
let n10b: GeneratorTm   = unAp Ap.n10b
let n20: GeneratorTm    = unAp Ap.n20
let n20b: GeneratorTm   = unAp Ap.n20b
let n21: GeneratorTm    = unAp Ap.n21
let n21b: GeneratorTm   = unAp Ap.n21b
let n22: GeneratorTm    = unAp Ap.n22
let n22b: GeneratorTm   = unAp Ap.n22b
let n100: GeneratorTm   = unAp Ap.n100
let n100b: GeneratorTm  = unAp Ap.n100b
let n10k: GeneratorTm   = unAp Ap.n10k
let n10kb: GeneratorTm  = unAp Ap.n10kb
let n100k: GeneratorTm  = unAp Ap.n100k
let n100kb: GeneratorTm = unAp Ap.n100kb
let n1M: GeneratorTm    = unAp Ap.n1M
let n1Mb: GeneratorTm   = unAp Ap.n1Mb
let n2M: GeneratorTm    = unAp Ap.n2M
let n2Mb: GeneratorTm   = unAp Ap.n2Mb
let n5M: GeneratorTm    = unAp Ap.n5M
let n5Mb: GeneratorTm   = unAp Ap.n5Mb
let n10M: GeneratorTm   = unAp Ap.n10M
let n10Mb: GeneratorTm  = unAp Ap.n10Mb