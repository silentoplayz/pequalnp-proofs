import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3843_381
    (pad : ∀ (copy : Fin 26 → (Fin 3 × Fin 26 × Fin 26)) (gs : List (Fin 3 × Fin 26 × Fin 26)) (out : Fin 26),
      gs.length ≤ 13 → out.val < 11 + gs.length →
      ∃ padded : List (Fin 3 × Fin 26 × Fin 26), padded.length = 13 ∧
        ∀ (w : List Bool) (step : List Bool → (Fin 3 × Fin 26 × Fin 26) → List Bool),
          (∀ v g, ∃ b : Bool, step v g = v ++ [b]) →
          (∀ v, out.val < v.length → step v (copy out) = v ++ [v.getD out.val false]) →
          w.length = 11 →
          (padded.foldl step w).getD 23 false = (gs.foldl step w).getD out.val false)
    (fixed : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x2 x3 x4 : Fin (26 : ℕ)) (x5 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x6 < (512 : ℕ),     have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x6.testBit ↑x8;     have x9 : List Bool → Fin (26 : ℕ) → Bool := fun (x9 : List Bool) (x10 : Fin (26 : ℕ)) => if ↑x10 = (25 : ℕ) then Bool.true else x9.getD (↑x10) Bool.false;     have x10 : List Bool := List.foldl (fun (x10 : List Bool) (x11 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x10 ++ [if ↑x11.1 = (0 : ℕ) then x9 x10 x11.2.1 && x9 x10 x11.2.2 else if ↑x11.1 = (1 : ℕ) then x9 x10 x11.2.1 || x9 x10 x11.2.2 else !x9 x10 x11.2.1]) (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x2, x3) :: x5);     x10.getD (↑x4) Bool.false = x1 x8; have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x3 x4 : Fin (26 : ℕ)) => ↑x3 < (9 : ℕ) ∧ ↑x4 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x3 + ↑x4) = Bool.true; ∀ (a b : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)), gs.length = 13 → x3 a b → ¬ x2 a b (23 : Fin 26) gs) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x2 x3 x4 : Fin (26 : ℕ)) (x5 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x6 < (512 : ℕ),     have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x6.testBit ↑x8;     have x9 : List Bool → Fin (26 : ℕ) → Bool := fun (x9 : List Bool) (x10 : Fin (26 : ℕ)) => if ↑x10 = (25 : ℕ) then Bool.true else x9.getD (↑x10) Bool.false;     have x10 : List Bool := List.foldl (fun (x10 : List Bool) (x11 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x10 ++ [if ↑x11.1 = (0 : ℕ) then x9 x10 x11.2.1 && x9 x10 x11.2.2 else if ↑x11.1 = (1 : ℕ) then x9 x10 x11.2.1 || x9 x10 x11.2.2 else !x9 x10 x11.2.1]) (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x2, x3) :: x5);     x10.getD (↑x4) Bool.false = x1 x8; have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x3 x4 : Fin (26 : ℕ)) => ↑x3 < (9 : ℕ) ∧ ↑x4 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x3 + ↑x4) = Bool.true; ∀ (x4 x5 x6 : Fin (26 : ℕ)) (x7 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x7.length ≤ (13 : ℕ) → x3 x4 x5 → ¬x2 x4 x5 x6 x7 := by
  intro target correct allowed a b out gs budget admissible agrees
  let init (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2
      else !read w g.2.1]
  let base (x : Fin 9 → Bool) := step (init x) (1,a,b)
  have baseLength (x : Fin 9 → Bool) : (base x).length = 11 := by
    simp [base,step,init]
  have append (v : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :
      ∃ b : Bool, step v g = v ++ [b] := ⟨_,rfl⟩
  have len (cs : List (Fin 3 × Fin 26 × Fin 26)) (v : List Bool) :
      (cs.foldl step v).length = v.length + cs.length := by
    induction cs generalizing v with
    | nil => simp
    | cons c cs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have agreesOn (n : ℕ) (hn : n < 512) :
      (gs.foldl step (base (fun i => n.testBit i.val))).getD out.val false =
      target (fun i => n.testBit i.val) := agrees n hn
  have live : out.val < 11 + gs.length := by
    by_contra h
    let x : Fin 9 → Bool := fun i => (3 : ℕ).testBit i.val
    have ht : target x = true := by decide
    have hf := agreesOn 3 (by decide)
    change (gs.foldl step (base x)).getD out.val false = target x at hf
    rw [List.getD_eq_default _ _ (by simpa [len,baseLength] using Nat.le_of_not_gt h), ht] at hf
    contradiction
  let copy (i : Fin 26) : Fin 3 × Fin 26 × Fin 26 := (1,i,i)
  have outNe : out.val ≠ 25 := by omega
  obtain ⟨padded,hsize,hpad⟩ := pad copy gs out budget live
  apply fixed a b padded hsize admissible
  intro n hn
  change (padded.foldl step (base (fun i => n.testBit i.val))).getD 23 false = _
  rw [hpad _ step append ?_ (baseLength _)]
  · exact agreesOn n hn
  · intro v hi
    simp [step,copy,read,outNe]
