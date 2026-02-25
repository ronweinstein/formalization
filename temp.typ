#import "style.typ":*
#show raw: set text(font: "Fira Code", weight: 450)

(some notes and scribbles to self)

- using the v1.9 semantics #link("https://www.desmos.com/api/v1.9/docs/index.html")
- no lists/subtyping
- generate constraints for each expressions 
- - model freevars
- - - name, constraint(s)
examples
#desmo(
  $c = a + b$,
)

```ml
 Add<T ∈ { Num, Vec2, Vec3 }>(T, T) -> T
 'a = 'b = 'c ∈ Add
```

#desmo(
  $c = a + b$,
  $f(a,b) = c^2$,
  $f(1, f(2, 3))$
)

```ml
a, b, c ∈ Add, 'a = 'b = 'c
f (inner):
  a_1 = 2, b_1 = 3, c_1 = 5
f (outer):
  a_2 = 1, b_2 = c_1 = 5, c_2 = 6
```
- wackscopes have to be type generalizeable?
```ml
let id x = x  -- id: 'a. 'a -> 'a
let a = id 5 in id true --
```
- `id` gets generalized to `int -> int` and `bool -> bool` (relavant terms: "type schemes", "let polymorphism"?)



```ml
type Primitive = 
  | Number
  | Point
  | Polygon

type ListType = 
  | Primitive Primitive
  | List (List Primitive)

type Type = 
  | Primitive Primitive
  | List (List CoreType)
  | Func (List CoreType -> CoreType)

```


#pagebreak()

```ml
type Type = 
  | Number
  | Point
  | Bool

type Ops = 
  | Point : (N, N) -> P
  | Add : (N, N) -> N | (P, P) -> P  
  | Sub : (N, N) -> N | (P, P) -> P
  | Dot : ((N, N) | (P, P) -> N) | ((N, P) | (P, N) -> P)
  | Eq  : (N, N) -> B
  | Leq : (N, N) -> B

type Expr = 
  | Var(str)
  | Const(number)
  | Call2(fn, Expr, Expr)

struct Fun2 =
  x : str
  y : str
  body : Expr


type WackEnv = str -> Option Expr
type FuncEnv = str -> Type

let infer expr =  
  | Var x => if x in WackEnv then infer WackEnv.x else any
  | Const => { number }
  | Call2 f x y => 
      let tx = infer x
      let ty = infer y
      let tf = infer f
      tf.find(e => e.args match [tx, ty]).then(e => e.body)

-- str -> str -> Expr -> FnSignature
infer_fun x y body =



```