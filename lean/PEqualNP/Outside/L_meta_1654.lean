import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1654

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wf gs x := rfl

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

def Cap {n L : ℕ} (line : Fin L → Finset (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c →
    ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j

theorem ind_subset_mono (n : ℕ) (S T : Finset (Fin n)) (h : S ⊆ T) :
    ∀ i, (List.ofFn (fun u : Fin n => decide (u ∈ S))).getD i false = true →
      (List.ofFn (fun u : Fin n => decide (u ∈ T))).getD i false = true := by
  intro i hi
  exact ofFn_mono n _ _ (by
    intro u hu
    simp only [decide_eq_true_eq] at hu ⊢
    exact h hu) i hi

theorem ind_point_mono (n : ℕ) (v : Fin n) (S : Finset (Fin n)) (h : v ∈ S) :
    ∀ i, (List.ofFn (fun u : Fin n => decide (u = v))).getD i false = true →
      (List.ofFn (fun u : Fin n => decide (u ∈ S))).getD i false = true := by
  intro i hi
  exact ofFn_mono n _ _ (by
    intro u hu
    simp only [decide_eq_true_eq] at hu ⊢
    exact hu ▸ h) i hi

end PEqualNP.Outside.L_meta_1654

open PEqualNP.Outside.L_meta_1654
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1654 :
    ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  intro n L line l gates G K I hUniq hMeet hleg hback hno hdisjI hcapI hK v hvl hG
  have hnoC : ¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧ Cap line X ∧
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true := hno
  have hcapIC : Cap line I := hcapI
  have mono_sub : ∀ (S T : Finset (Fin n)) (o : ℕ), S ⊆ T →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ S)))).getD o false = true →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ T)))).getD o false = true := by
    intro S T o hST hS
    rw [wires_eq] at hS ⊢
    exact mono2 gates hleg _ _ (by simp) (ind_subset_mono n S T hST) o hS
  have mono_pt : ∀ (v' : Fin n) (T : Finset (Fin n)) (o : ℕ), v' ∈ T →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v')))).getD o false = true →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ T)))).getD o false = true := by
    intro v' T o hvT hS
    rw [wires_eq] at hS ⊢
    exact mono2 gates hleg _ _ (by simp) (ind_point_mono n v' T hvT) o hS
  have hvnotI : v ∉ I := by
    intro hvI
    apply hnoC
    exact ⟨I, hdisjI, hcapIC, mono_pt v I G hvI hG, hK⟩
  have hfail : ¬ Cap line (I ∪ {v}) := by
    intro hcapU
    apply hnoC
    refine ⟨I ∪ {v}, ?_, hcapU, ?_, ?_⟩
    · refine Finset.disjoint_left.mpr ?_
      intro x hx hxl
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.disjoint_left.mp hdisjI h) hxl
      · have hxv : x = v := by simpa using h
        exact hvl (hxv ▸ hxl)
    · exact mono_pt v (I ∪ {v}) G (Finset.mem_union_right I (Finset.mem_singleton_self v)) hG
    · exact mono_sub I (I ∪ {v}) K (Finset.subset_union_left) hK
  unfold Cap at hfail
  have htriple : ∃ a, a ∈ I ∪ {v} ∧ ∃ b, b ∈ I ∪ {v} ∧ ∃ c, c ∈ I ∪ {v} ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j := by
    by_contra hcon
    exact hfail (by
      intro a ha b hb c hc hab hac hbc hcol
      exact hcon ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hcol⟩)
  obtain ⟨a, haS, b, hbS, c, hcS, hab', hac', hbc', j, haj, hbj, hcj⟩ := htriple
  have memI_of : ∀ x, x ∈ (I ∪ {v} : Finset (Fin n)) → x ≠ v → x ∈ I := by
    intro x hx hxv
    rcases Finset.mem_union.mp hx with h | h
    · exact h
    · exact absurd (by simpa using h) hxv
  have hsome : a = v ∨ b = v ∨ c = v := by
    by_contra hcon
    push_neg at hcon
    exact hcapIC a (memI_of a haS hcon.1) b (memI_of b hbS hcon.2.1)
      c (memI_of c hcS hcon.2.2) hab' hac' hbc' ⟨j, haj, hbj, hcj⟩
  refine ⟨hvnotI, ?_⟩
  rcases hsome with hav | hbv | hcv
  · refine ⟨b, memI_of b hbS (fun h => hab' (hav.trans h.symm)), c,
      memI_of c hcS (fun h => hac' (hav.trans h.symm)), hbc', j, hbj, hcj, ?_⟩
    rw [← hav]; exact haj
  · refine ⟨a, memI_of a haS (fun h => hab' (h.trans hbv.symm)), c,
      memI_of c hcS (fun h => hbc' (hbv.trans h.symm)), hac', j, haj, hcj, ?_⟩
    rw [← hbv]; exact hbj
  · refine ⟨a, memI_of a haS (fun h => hac' (h.trans hcv.symm)), b,
      memI_of b hbS (fun h => hbc' (h.trans hcv.symm)), hab', j, haj, hbj, ?_⟩
    rw [← hcv]; exact hcj
