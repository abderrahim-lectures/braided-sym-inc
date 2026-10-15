/-! Dimensions of BSDer_{sigma_alpha}(I(P))^alpha and Der(I(P))^alpha over F_p for small posets.
Each `#guard` checks one entry of the table in paper/maths/braided-sym-inc. -/
namespace Research.BraidedSymInc
-- dim of BSDer_{sigma_alpha}(I(P))^alpha and Der(I(P))^alpha over F_p, small posets
def modp (p : Nat) (a : Int) : Nat := (a % (p : Int)).toNat

def inv (p a : Nat) : Nat := Id.run do
  let mut r := 0
  for t in [1:p] do
    if (a * t) % p == 1 then r := t
  return r

def rank (p : Nat) (rows : Array (Array Nat)) (ncols : Nat) : Nat := Id.run do
  let mut M := rows
  let mut r := 0
  for c in [0:ncols] do
    let mut piv : Option Nat := none
    for i in [r:M.size] do
      if piv.isNone && M[i]![c]! % p != 0 then piv := some i
    match piv with
    | none => pure ()
    | some i =>
      let tmp := M[i]!
      M := M.set! i M[r]!
      M := M.set! r tmp
      let iv := inv p (M[r]![c]!)
      M := M.set! r ((M[r]!).map fun x => (x * iv) % p)
      for j in [0:M.size] do
        if j != r && M[j]![c]! % p != 0 then
          let f := M[j]![c]!
          M := M.set! j (Array.ofFn (n := ncols) fun t =>
            modp p ((M[j]![t]! : Int) - (f * M[r]![t]! : Nat)))
      r := r + 1
  return r

structure Poset where
  n : Nat
  le : Nat → Nat → Bool
  tau : Nat → Nat

def Poset.pairs (P : Poset) : Array (Nat × Nat) := Id.run do
  let mut a := #[]
  for x in [0:P.n] do
    for y in [0:P.n] do
      if P.le x y then a := a.push (x, y)
  return a

-- structure constants: product of basis elements i,j as list of basis indices
def Poset.prod (P : Poset) (b : Array (Nat × Nat)) (i j : Nat) : List Nat :=
  if (b[i]!).2 == (b[j]!).1 then
    match b.findIdx? (· == ((b[i]!).1, (b[j]!).2)) with
    | some k => [k]
    | none => []
  else []

def Poset.alpha (P : Poset) (b : Array (Nat × Nat)) (i : Nat) : Nat :=
  (b.findIdx? (· == (P.tau (b[i]!).1, P.tau (b[i]!).2))).getD 0

def dims (p : Nat) (P : Poset) : Nat × Nat := Id.run do
  let b := P.pairs
  let m := b.size
  let N := m * m
  let u := fun (k i : Nat) => k * m + i
  -- twisted product: ij + alpha(j) alpha(i)
  let cT := fun (i j : Nat) => P.prod b i j ++ P.prod b (P.alpha b j) (P.alpha b i)
  let cP := fun (i j : Nat) => P.prod b i j
  let build := fun (c : Nat → Nat → List Nat) => Id.run do
    let mut rows : Array (Array Nat) := #[]
    for i in [0:m] do
      for j in [0:m] do
        for k in [0:m] do
          let mut row : Array Int := Array.replicate N 0
          for l in c i j do row := row.modify (u k l) (· + 1)
          for q in [0:m] do
            for l in c q j do
              if l == k then row := row.modify (u q i) (· - 1)
            for l in c i q do
              if l == k then row := row.modify (u q j) (· - 1)
          rows := rows.push (row.map (modp p))
    for k in [0:m] do
      for i in [0:m] do
        let mut row : Array Int := Array.replicate N 0
        row := row.modify (u (P.alpha b k) (P.alpha b i)) (· + 1)
        row := row.modify (u k i) (· - 1)
        rows := rows.push (row.map (modp p))
    return rows
  let rB := rank p (build cT) N
  let rD := rank p (build cP) N
  return (N - rB, N - rD)

def chain (n : Nat) (t : Nat → Nat) : Poset := ⟨n, fun x y => x ≤ y, t⟩
def vee : Poset := ⟨3, fun x y => x == y || x == 0, id⟩
def veeSwap : Poset := ⟨3, fun x y => x == y || x == 0, fun x => if x == 1 then 2 else if x == 2 then 1 else x⟩
def anti2 : Poset := ⟨2, fun x y => x == y, fun x => 1 - x⟩
def diamondSwap : Poset :=
  ⟨4, fun x y => x == y || x == 0 || y == 3, fun x => if x == 1 then 2 else if x == 2 then 1 else x⟩


-- 5-element cross: 0,1 < 2 < 3,4, swap 0<->1 and 3<->4
def cross : Poset :=
  ⟨5, fun x y => x == y || (x ≤ 1 && y ≥ 2) || (x == 2 && y ≥ 3),
   fun x => if x == 0 then 1 else if x == 1 then 0 else if x == 3 then 4 else if x == 4 then 3 else x⟩

#guard dims 2 anti2 == (1, 0)
#guard dims 3 anti2 == (0, 0)
#guard dims 2 (chain 2 id) == (4, 2)
#guard dims 3 (chain 2 id) == (2, 2)
#guard dims 2 (chain 3 id) == (8, 5)
#guard dims 3 (chain 3 id) == (5, 5)
#guard dims 2 vee == (7, 4)
#guard dims 3 vee == (4, 4)
#guard dims 2 veeSwap == (3, 2)
#guard dims 3 veeSwap == (2, 2)
#guard dims 2 diamondSwap == (6, 5)
#guard dims 3 diamondSwap == (5, 5)
#guard dims 2 cross == (6, 6)
#guard dims 3 cross == (6, 6)

end Research.BraidedSymInc
