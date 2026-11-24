import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4125_381 (flip : ∀ (n : ℕ) (f : (Fin n → Bool) → Prop),
      (∀ x y, (∀ i, x i = true → y i = true) → f x → f y) →
      ∀ x, (∀ y, (∀ i, x i = true → y i = true) → x ≠ y → f y) ↔
        ∀ i, x i = false → f (fun j => if j = i then true else x j))
    (witness : have x1 : (Fin 14 → Bool) → Prop := fun (x1 : Fin 14 → Bool) => ∃ (x2 : Fin 7) (x3 : Fin 7), (x2 = x3 ∨ x2 = x3 + (1 : Fin 7) ∨ x2 = x3 + (3 : Fin 7)) ∧ x1 (Fin.castAdd 7 x2) = Bool.true ∧ x1 (Fin.natAdd 7 x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ 27 ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < 14 + x3 ∧ x7 < 14 + x3) ∧ (∀ (x3 x4 : Fin 7), x3 = x4 ∨ x3 = x4 + (1 : Fin 7) ∨ x3 = x4 + (3 : Fin 7) → x2.eval (List.ofFn fun (x6 : Fin 14) => Decidable.decide (x6 = Fin.castAdd 7 x3 ∨ x6 = Fin.natAdd 7 x4)) = Bool.true) ∧ (∀ (x3 : Fin 14 → Bool), ¬x1 x3 → (∀ i : Fin 14, x3 i = false → x1 (fun j => if j = i then true else x3 j)) → x2.eval (List.ofFn x3) = Bool.false) ∧ ∀ (x3 : Bool), ((PEqualNP.ReadK.linearParts x2 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then 7 else (0 : ℕ))) (List.ofFn fun (x4 : Fin 14) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = 7))).getD x2.output (Bool.false, Bool.false)).2 = Bool.false) :
have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → x2.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) ∧ (∀ (x3 : Fin (14 : ℕ) → Bool), ¬x1 x3 → (∀ (x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x3 x6 = Bool.true → x5 x6 = Bool.true) → x3 ≠ x5 → x1 x5) → x2.eval (List.ofFn x3) = Bool.false) ∧ ∀ (x3 : Bool), ((PEqualNP.ReadK.linearParts x2 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x2.output (Bool.false, Bool.false)).2 = Bool.false := by
  classical
  intro incidence
  obtain ⟨C,size,legal,edges,negative,reread⟩ := witness
  refine ⟨C,size,legal,edges,?_,reread⟩
  intro x independent maximal
  have grow (x y : Fin 14 → Bool) (le : ∀ i, x i = true → y i = true) :
      incidence x → incidence y := by
    rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,l,edge,le _ hp,le _ hl⟩
  exact negative x independent ((flip 14 incidence grow x).mp maximal)
