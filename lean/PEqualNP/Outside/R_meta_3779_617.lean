import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.GenericRejection PEqualNP.HeptadCover in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3779_617
    (erase : ∀ (n : ℕ) (C : Circuit) (T : Bool → List Bool → Prop) (j : ℕ),
      Monotone2 C → ReadsBack n C → j < C.size → C.output ≠ n+j →
      (∀ b x, T b x → x.length = n ∧ C.eval x = b) →
      (∀ x, T true x → (C.wires x).getD (n+j) false = false) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
        ∀ b x, T b x → D.eval x = b)
    (core :
      let S := singerLines3
      let good := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q)) = false
      let inside := fun (C : Circuit) i j =>
        (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j
      ∀ C : Circuit, good C → C.size < 64 →
        (∀ i j, inside C i j → ∃ Q, IsQuadrangle S Q ∧
          (C.wires (incidenceInput Q (missLines S Q))).getD (26+i) false = true) →
        (∀ i j, inside C i j → ∃ l p, p ∈ S l ∧
          (C.wires (incidenceInput {p} {l})).getD (26+i) false = true) →
        (∃ i j, inside C i j) →
        (∀ g ∈ C.gates, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        ∃ D : Circuit, good D ∧ D.size < C.size) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 → x5.size < (64 : ℕ) → (∀ (x8 x9 : ℕ), x4 x5 x8 x9 → ∃ (x11 : List Bool), x2 Bool.false x11 ∧ (x5.wires x11).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (∃ (x9 : ℕ) (x10 : ℕ), x4 x5 x9 x10) → (∀ x10 ∈ x5.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x3 x11 ∧ x11.size < x5.size
 := by
  classical
  intros differences tests correct inside C hC size dirty nested clean
  let S := singerLines3
  have geometry : ∀ p l : Fin 13,
      p ∈ singerLines3 l ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13)) := by decide
  have incidence (p l : Fin 13) : p ∈ S l ↔ p-l ∈ differences := geometry p l
  have rowPos (p l : Fin 13) : incidenceInput {p} {l} =
      (List.ofFn fun q : Fin 13 => decide (q = p)) ++
      (List.ofFn fun q : Fin 13 => decide (q = l)) := by
    change List.ofFn (fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13)))) = _
    simp only [Finset.mem_singleton]
  have pos (p l : Fin 13) (inc : p ∈ S l) : tests true (incidenceInput {p} {l}) := by
    have e : p-l ∈ differences := (incidence p l).mp inc
    simp only [tests,ite_true]
    exact ⟨p,l,e,rowPos p l⟩
  have arc (Q : Finset (Fin 13)) : IsQuadrangle S Q ↔
      Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p-l ∈ differences).card ≤ 2 := by
    have eq (l : Fin 13) : Q ∩ S l = Q.filter (fun p => p-l ∈ differences) := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter,incidence]
    change (Q.card = 4 ∧ ∀ l : Fin 13, (Q ∩ S l).card ≤ 2) ↔ _
    simp only [eq]
  have miss (Q : Finset (Fin 13)) (l : Fin 13) : l ∈ missLines S Q ↔ ∀ p ∈ Q, p-l ∉ differences := by
    constructor
    · intro m p hp inc
      exact Finset.disjoint_left.mp (Finset.mem_filter.mp m).2
        ((incidence p l).mpr inc) hp
    · intro off
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mpr ?_⟩
      intro p inc hit
      exact off p hit ((incidence p l).mp inc)
  have rowEq (Q : Finset (Fin 13)) :
      incidenceInput Q (missLines S Q) =
        (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        (List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ differences)) := by
    have eq (l : Fin 13) : decide (l ∈ missLines S Q) =
        decide (∀ p ∈ Q, p-l ∉ differences) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using miss Q l
    change (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      (List.ofFn fun l : Fin 13 => decide (l ∈ missLines S Q)) = _
    simp only [eq]
  have neg (Q : Finset (Fin 13)) (q : IsQuadrangle S Q) :
      tests false (incidenceInput Q (missLines S Q)) := by
    simp only [tests,Bool.false_eq_true,ite_false]
    exact ⟨Q,((arc Q).mp q).1,((arc Q).mp q).2,rowEq Q⟩
  have testLen (b : Bool) (x : List Bool) (hx : tests b x) : x.length = 26 := by
    cases b
    · simp only [tests,Bool.false_eq_true,ite_false] at hx
      obtain ⟨Q,_,_,rfl⟩ := hx
      simp
    · simp only [tests,ite_true] at hx
      obtain ⟨p,l,_,rfl⟩ := hx
      simp
  have mine : tests true (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))) := by
    apply pos
    decide
  by_cases off : ∃ i j, inside C i j ∧
      ∀ x, tests true x → (C.wires x).getD (26+i) false = false
  · obtain ⟨i,j,dormant,h⟩ := off
    have iValid : i < C.size := by
      by_contra! past
      have op := dormant.1
      change C.gates.length ≤ i at past
      unfold gateAt at op
      rw [List.getD_eq_default _ _ past] at op
      cases op
    have notOut : C.output ≠ 26+i := by
      intro eq
      have yes := hC.2.2 true _ mine
      change (C.wires _).getD C.output false = true at yes
      rw [eq,h _ mine] at yes
      contradiction
    obtain ⟨D,mono,back,lt,passes⟩ := erase 26 C tests i hC.1 hC.2.1 iValid notOut
      (fun b x ht => ⟨testLen b x ht,hC.2.2 b x ht⟩) h
    exact ⟨D,⟨mono,back,passes⟩,lt⟩
  · have good : Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q)) = false :=
      ⟨hC.1,hC.2.1,fun l p inc => hC.2.2 true _ (pos p l inc),
        fun Q q => hC.2.2 false _ (neg Q q)⟩
    have negative (i j : ℕ) (hp : inside C i j) :
        ∃ Q, IsQuadrangle S Q ∧ (C.wires (incidenceInput Q (missLines S Q))).getD (26+i) false = true := by
      obtain ⟨x,hx,yes⟩ := dirty i j hp
      simp only [tests,Bool.false_eq_true,ite_false] at hx
      obtain ⟨Q,card,cap,rfl⟩ := hx
      exact ⟨Q,(arc Q).mpr ⟨card,cap⟩,by simpa only [rowEq Q] using yes⟩
    have positive (i j : ℕ) (hp : inside C i j) :
        ∃ l p, p ∈ S l ∧ (C.wires (incidenceInput {p} {l})).getD (26+i) false = true := by
      by_contra! absent
      apply off
      refine ⟨i,j,hp,?_⟩
      intro x test
      simp only [tests,ite_true] at test
      obtain ⟨p,l,e,rfl⟩ := test
      have gone := absent l p ((incidence p l).mpr e)
      rw [rowPos p l] at gone
      exact Bool.eq_false_of_not_eq_true gone
    obtain ⟨D,⟨mono,back,accept,reject⟩,lt⟩ := core C good size negative positive nested clean
    refine ⟨D,⟨mono,back,?_⟩,lt⟩
    intro b x ht
    cases b
    · simp only [tests,Bool.false_eq_true,ite_false] at ht
      obtain ⟨Q,card,cap,row⟩ := ht
      calc
        D.eval x = D.eval (incidenceInput Q (missLines S Q)) :=
          congrArg D.eval (row.trans (rowEq Q).symm)
        _ = false := reject Q ((arc Q).mpr ⟨card,cap⟩)
    · simp only [tests,ite_true] at ht
      obtain ⟨p,l,e,row⟩ := ht
      have row' : x = incidenceInput {p} {l} := row.trans (rowPos p l).symm
      exact (congrArg D.eval row').trans
        (accept l p ((incidence p l).mpr e))
