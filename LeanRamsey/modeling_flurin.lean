import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Nth



set_option autoImplicit false
set_option tactic.hygienic false


def Family (n s : ℕ) := (Fin s) → Finset (Fin n)


def K_L_Family {n s: ℕ} (F : Family n s) (k : ℕ) (L : Finset ℕ)  : Prop :=
  -- Each Set has size k
  ∀ i : Fin s,  (F i).card = k ∧
  -- Each intersection is in L (also the sets are distinct)
  ∀ i j  : Fin s, i ≠ j → ((F i) ≠ (F j) ∧ ((F i) ∩ (F j)).card ∈ L)

def K_P_L_Family  {n s: ℕ} (F : Family n s) (k p : ℕ)  (L : Finset ℕ)  : Prop :=
    Nat.Prime p ∧  -- p is prime
    ∀ i : Fin s, Nat.mod (F i).card p = k  ∧  -- set sizes (mod p) are not in L --
    -- Each intersection is in L (also the sets are distinct)
    ∀ i j : Fin s, i ≠ j → ((F i) ≠ (F j) ∧ Nat.mod ((F i) ∩ (F j)).card p ∈ L)


-- This is the first theorem we need (we do prove this one)
theorem RayChaudhuriWilson {n s k : ℕ} {L : Finset ℕ}
    {F : Family n s} (ℱ : K_L_Family F k L) :
    (∀ x ∈ L, x < k) → Fintype.card (Fin s) ≤ (Nat.choose n (L.card)) := by
    intros
    sorry

-- This is the second theorem we need (we omit the proof of this theorem)
theorem AlonBabaiSuzuki  {n s p k : ℕ} {L : Finset ℕ} {F : Family n s} (ℱ : K_P_L_Family F k p L) :
    Nat.mod k p ∉ L ∧ L.card ≤ (p-1) ∧ L.card + k ≤ n →  Fintype.card (Fin s) ≤ (Nat.choose n (L.card)) := by
    sorry

----- Put above in seprate File
variable {α : Type}

-- G is a graph with n vertices and no k + 1 clique or k + 1 IS
def ExplictDiagonalRamsey (G:  SimpleGraph (α)) [Fintype α] [DecidableRel G.Adj] (n k : ℕ): Prop := (n = Fintype.card α) ∧  ¬ ((∃ S, G.IsNClique k S) ∨ (∃ T, Gᶜ.IsNClique k T))

-- Vertex Set
-- Subsets of [p^3] with cardinality p^2 - 1
def vertices (p : ℕ) :=
  { A : Finset (Fin (p^3)) // A.card = p^2 - 1 }

-- Fintype instance (asked ChatGppt here)
instance (p : ℕ) : Fintype (vertices p) :=
  Subtype.fintype (fun A : Finset (Fin (p^3)) => A.card = p^2 - 1)

def construction (p : ℕ)  [Fintype (vertices p)]  : SimpleGraph (vertices p) :=
    { Adj := fun A B =>
        Nat.mod (A.val ∩ B.val).card p = p - 1 ∧ A ≠ B,
        symm := by
        grw[Symmetric]
        intros
        simp at *
        obtain ⟨h1, h2⟩ := a
        constructor
        grw[<-h1, Finset.inter_comm]
        intro
        grw[a] at h2
        contradiction
         ,
        loopless := by
        grw[Irreflexive]
        simp at *
    }

instance verticesDecEq (p : ℕ) : DecidableEq (vertices p) := by
    exact Subtype.instDecidableEq

instance (p : ℕ) : DecidableRel (construction p).Adj := by
    grw[DecidableRel]
    intros
    grw[construction]
    simp
    exact instDecidableAnd


lemma isExplicitRamsey (p : ℕ):  Nat.Prime p → (ExplictDiagonalRamsey (construction p) (Nat.choose (p^3) ((p^2) - 1)) ((Nat.choose (p^3) (p-1) )+ 1))  := by

    intro -- We recover the actual statement in a "convinient form"
    set n := Nat.choose (p^3) ((p^2) - 1)
    set k := Nat.choose (p^3) (p-1)
    grw[ExplictDiagonalRamsey]

    constructor -- We need to Graph has  n = ... vertices, no k + 1 clique and no k + 1 IS
    dsimp [vertices]
    grw[Fintype.card_subtype]
    simp_all only [Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, n]

    simp
    constructor --We need to show no Clique and no IS
    all_goals -- Simplify statement a bit
        intros
        grw[Not]
        intro


    have hx_card : x.card = k + 1:= a_1.card_eq
    have hx_adj :  ∀ ⦃v w : vertices p⦄, v ∈ x → w ∈ x → v ≠ w → (construction p).Adj v w :=   fun v w hv hw hneq => a_1.isClique hv hw hneq

    let l := x.toList
    have hlen : l.length = x.card := (Finset.length_toList x)
    have h_ndup : l.Nodup := Finset.nodup_toList x
    have F : Family (p^3) (k + 1) := fun (indices : Fin (k + 1)) =>
        (l.get ⟨indices.val, by rw [hlen, hx_card]; exact indices.is_lt⟩).val

    let L : Finset ℕ :=
    (Finset.range (p^2)).filter
        (fun x : ℕ =>
        ∃ y : Fin p, y.val * (p - 1) = x);

    have h :  K_L_Family F ((p^2) - 1) L := by
        grw[K_L_Family]
        intro
        constructor
        sorry
        intros
        constructor
        sorry
        sorry
    apply RayChaudhuriWilson at h
    have hL :  ∀ x ∈ L, x < p.pow 2 - 1 := by
        intros
        sorry
    apply h at hL
    have hLcard : L.card = (p-1) := by sorry
    simp[hLcard] at *
    grind


    have hx_card : x.card = k + 1:= a_1.card_eq
    have hx_not_adj :  ∀ ⦃v w : vertices p⦄, v ∈ x → w ∈ x → v ≠ w → ¬(construction p).Adj v w :=   fun v w hv hw hneq => a_1.isIndepSet hv hw hneq

    let l := x.toList
    have hlen : l.length = x.card := (Finset.length_toList x)
    have h_ndup : l.Nodup := Finset.nodup_toList x
    have F : Family (p^3) (k + 1) := fun (indices : Fin (k + 1)) =>
        (l.get ⟨indices.val, by rw [hlen, hx_card]; exact indices.is_lt⟩).val
    let L : Finset ℕ := (Finset.range (p-1))
    have h :  K_P_L_Family F ((p^2) - 1) p L := by
        grw[K_P_L_Family]
        constructor
        exact a
        intros
        constructor
        sorry
        intros
        constructor
        sorry
        sorry
    apply AlonBabaiSuzuki at h
    have hLcard : L.card = (p-1) := by sorry
    have hL : (p ^ 2 - 1).mod p ∉ L ∧ L.card ≤ p - 1 ∧ L.card + (p ^ 2 - 1) ≤ p ^ 3 := by
        constructor
        sorry
        constructor
        omega
        grw[hLcard]
        sorry
    apply h at hL
    simp at *
    grind


















-- Want a Statement A(p) produces a graph (given p is prime)
-- which is (p^3 choose p - 1) ramsey
