/-
  Wolstenholme's theorem: C(2p, p) ≡ 2 (mod p³) for prime p ≥ 5.

  Complete, self-contained proof — zero sorry, zero axiom.

  Architecture:
  1. sum_pow_Icc_zmod_eq_zero — ∑_{j=1}^{p-1} j^k = 0 in ZMod p for 1≤k≤p-2
     Via: sum_Icc_eq_sum_erase_zero (bridge) + g·x multiplication trick
  2. sum_pow_dvd — p | ∑_{j=1}^{p-1} j^k in ℤ (lift from ZMod p)
  3. harmonic_sum_dvd_sq — p² | ∑ (p-1)!/j for p ≥ 5
     Via: pairing j↔p-j to factor out p, then sum_pow_dvd with k=p-3.
  4. e2_prod_cons + prod_shift_expansion_2 — second-order expansion
     Via: Finset.cons_induction, e₂ recurrence, ring closure.
  5. p_dvd_e2_prod — p | e₂({1,…,p-1})
     Via: Wilson + Fermat + algebraic identity + power sum vanishing.
  6. prod_shift_mod_cube — p³ | ∏(p+k) - (p-1)!
     Via: first-order expansion + harmonic divisibility + second-order expansion + e₂ divisibility.
  7. wolstenholme_binom — final assembly: C(2p,p) ≡ 2 (mod p³).
-/
import Mathlib

open Finset

-- ═══════════════════════════════════════════════════════════════
-- §1. Bridge: Icc 1 (p-1) ↔ univ.erase 0 in ZMod p
-- ═══════════════════════════════════════════════════════════════

/-- The sum over {1,...,p-1} (as naturals cast to ZMod p) equals the sum
over all nonzero elements of ZMod p. -/
private lemma sum_Icc_eq_sum_erase_zero {p : Nat} [hp : Fact (Nat.Prime p)] (k : Nat) :
    ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p)) ^ k =
    ∑ x ∈ univ.erase (0 : ZMod p), x ^ k := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply sum_nbij (fun (j : ℕ) => ((j : ℕ) : ZMod p))
  · intro j hj
    have hj' := mem_Icc.mp hj
    refine mem_erase.mpr ⟨?_, mem_univ _⟩
    intro h; rw [CharP.cast_eq_zero_iff (ZMod p) p] at h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · intro j₁ hj₁ j₂ hj₂ h
    have hj₁' := mem_Icc.mp hj₁; have hj₂' := mem_Icc.mp hj₂
    have := congr_arg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast,
         Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · intro x hx
    have hx' := (mem_erase.mp hx).1
    exact ⟨ZMod.val x,
      mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (fun hv =>
        hx' ((ZMod.val_eq_zero x).mp hv)),
        Nat.le_sub_one_of_lt (ZMod.val_lt x)⟩,
      ZMod.natCast_zmod_val x⟩
  · intro _ _; rfl

-- ═══════════════════════════════════════════════════════════════
-- §2. Power sum vanishing in ZMod p and ℤ
-- ═══════════════════════════════════════════════════════════════

/-- In ZMod p (p prime), ∑_{j=1}^{p-1} j^k = 0 for 1 ≤ k ≤ p-2.
Proof: multiply by g^k - 1 where g is a primitive root; the sum is
invariant under x ↦ g·x (a permutation of ZMod p), so (g^k-1)·S = 0,
and g^k ≠ 1 since orderOf g = p-1 doesn't divide k. -/
lemma sum_pow_Icc_zmod_eq_zero {p : Nat} [hp : Fact (Nat.Prime p)] (k : Nat)
    (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p)) ^ k = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [sum_Icc_eq_sum_erase_zero k]
  have hsplit : ∑ x : ZMod p, x ^ k =
      (0 : ZMod p) ^ k + ∑ x ∈ univ.erase (0 : ZMod p), x ^ k :=
    (add_sum_erase _ _ (mem_univ 0)).symm
  rw [zero_pow (by omega), zero_add] at hsplit
  rw [← hsplit]
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    have hall : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := by
      intro x; obtain ⟨n, hn⟩ := hg x; exact ⟨n, by exact_mod_cast hn⟩
    rw [orderOf_eq_card_of_forall_mem_zpowers hall,
        Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  have hgk_ne : g ^ k ≠ 1 := by
    intro h; have := orderOf_dvd_of_pow_eq_one h; rw [hord] at this
    have : p - 1 ≤ k := Nat.le_of_dvd (by omega) this; omega
  have hgvk_sub_ne : (g : ZMod p) ^ k - 1 ≠ 0 := by
    intro h; apply hgk_ne; ext; rw [Units.val_pow_eq_pow_val, Units.val_one, sub_eq_zero.mp h]
  have hperm : Function.Bijective ((g : ZMod p) * ·) :=
    (mul_left_surjective₀ (Units.ne_zero g)).bijective_of_finite
  have hshift : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [mul_sum]; simp_rw [← mul_pow]
    exact sum_equiv (Equiv.ofBijective _ hperm) (by intro _; simp) (by intro _ _; rfl)
  exact (mul_eq_zero.mp (by rw [sub_mul, one_mul, hshift, sub_self])).resolve_left hgvk_sub_ne

/-- p divides ∑_{j=1}^{p-1} j^k in ℤ, for 1 ≤ k ≤ p-2 and prime p. -/
lemma sum_pow_dvd (p : Nat) (hp : Nat.Prime p) (k : Nat)
    (hk1 : 1 ≤ k) (hk2 : k ≤ p - 2) :
    (p : ℤ) ∣ ∑ j ∈ Icc 1 (p - 1), ((j : ℤ)) ^ k := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  push_cast
  exact sum_pow_Icc_zmod_eq_zero k hk1 hk2

-- ═══════════════════════════════════════════════════════════════
-- §3. Wolstenholme harmonic sum — p² | ∑ (p-1)!/j for p ≥ 5
-- ═══════════════════════════════════════════════════════════════

private lemma sum_invol_reindex (p : Nat) (hp5 : p ≥ 5) (f : ℕ → ℤ) :
    ∑ j ∈ Icc 1 (p - 1), f (p - j) =
    ∑ j ∈ Icc 1 (p - 1), f j := by
  apply sum_nbij (fun j => p - j)
  · intro j hj; rw [mem_Icc] at hj ⊢; omega
  · intro j₁ hj₁ j₂ hj₂ (h : p - j₁ = p - j₂)
    simp only [coe_Icc, Set.mem_Icc] at hj₁ hj₂; omega
  · intro j hj; simp only [coe_Icc, Set.mem_Icc, Set.mem_image] at hj ⊢
    exact ⟨p - j, by omega, by omega⟩
  · intro j hj; rfl

private lemma harmonic_sum_dvd_sq (p : Nat) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (p : ℤ) ^ 2 ∣ ∑ j ∈ Icc 1 (p - 1),
      ∏ k ∈ (Icc 1 (p - 1)).erase j, (k : ℤ) := by
  set s := Icc 1 (p - 1)
  set f : ℕ → ℤ := fun j => ∏ k ∈ s.erase j, (k : ℤ)
  set P : ℤ := ∏ k ∈ s, (k : ℤ)
  -- Step 1: 2·S₁ = ∑(f j + f(p-j)) via the involution j ↦ p-j
  have h_reindex : ∑ j ∈ s, f (p - j) = ∑ j ∈ s, f j := sum_invol_reindex p hp5 f
  have h_2S : 2 * ∑ j ∈ s, f j = ∑ j ∈ s, (f j + f (p - j)) := by
    rw [sum_add_distrib, h_reindex, two_mul]
  -- Step 2: p | each (f j + f(p-j)) via pairing identity + coprimality
  have h_p_dvd_pair : ∀ j ∈ s, (p : ℤ) ∣ (f j + f (p - j)) := by
    intro j hj
    have hj' := mem_Icc.mp hj
    have hpj : p - j ∈ s := mem_Icc.mpr (by omega)
    have h1 : (j : ℤ) * f j = P := mul_prod_erase s (fun k => (k : ℤ)) hj
    have h2 : ((p : ℤ) - j) * f (p - j) = P := by
      rw [← show ((p - j : ℕ) : ℤ) = (p : ℤ) - (j : ℤ) from by omega]
      exact mul_prod_erase s (fun k => (k : ℤ)) hpj
    have hpair : (j : ℤ) * ((p : ℤ) - j) * (f j + f (p - j)) = (p : ℤ) * P := by
      nlinarith [h1, h2]
    have hcop : IsCoprime ((j : ℤ) * ((p : ℤ) - j)) (p : ℤ) := by
      rw [show (j : ℤ) * ((p : ℤ) - j) = ((j * (p - j) : ℕ) : ℤ) from by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : j ≤ p)]]
      exact_mod_cast (by
        apply Nat.Coprime.mul_left
        · exact (hp.coprime_iff_not_dvd.mpr (fun h =>
            absurd (Nat.le_of_dvd (by omega) h) (by omega))).symm
        · exact (hp.coprime_iff_not_dvd.mpr (fun h =>
            absurd (Nat.le_of_dvd (by omega) h) (by omega))).symm
        : Nat.Coprime (j * (p - j)) p).isCoprime
    exact hcop.symm.dvd_of_dvd_mul_left ⟨P, by linarith⟩
  -- Step 3: 2·S₁ = p · G for some G
  obtain ⟨G, hG⟩ : (p : ℤ) ∣ 2 * ∑ j ∈ s, f j := h_2S ▸ dvd_sum h_p_dvd_pair
  -- Step 4: p | G (the mathematical heart — G ≡ -P·∑j^{p-3} ≡ 0 mod p)
  have h_p_dvd_G : (p : ℤ) ∣ G := by
    set Q : ℕ → ℤ := fun j => (f j + f (p - j)) / (p : ℤ)
    have hQ_exact : ∀ j ∈ s, (p : ℤ) * Q j = f j + f (p - j) := by
      intro j hj
      show (p : ℤ) * ((f j + f (p - j)) / (p : ℤ)) = f j + f (p - j)
      rw [mul_comm]; exact Int.ediv_mul_cancel (h_p_dvd_pair j hj)
    have h_sum_Q : (p : ℤ) * G = (p : ℤ) * ∑ j ∈ s, Q j := by
      rw [← hG, h_2S]
      rw [show ∑ j ∈ s, (f j + f (p - j)) = ∑ j ∈ s, (p : ℤ) * Q j from
        sum_congr rfl (fun j hj => (hQ_exact j hj).symm)]
      rw [← mul_sum]
    have hG_eq : G = ∑ j ∈ s, Q j :=
      mul_left_cancel₀ (show (p : ℤ) ≠ 0 from by exact_mod_cast hp.ne_zero) h_sum_Q
    have hQ_rel : ∀ j ∈ s, (j : ℤ) * ((p : ℤ) - j) * Q j = P := by
      intro j hj
      have hj' := mem_Icc.mp hj
      have hpj : p - j ∈ s := mem_Icc.mpr (by omega)
      have h1 : (j : ℤ) * f j = P := mul_prod_erase s (fun k => (k : ℤ)) hj
      have h2 : ((p : ℤ) - j) * f (p - j) = P := by
        rw [← show ((p - j : ℕ) : ℤ) = (p : ℤ) - (j : ℤ) from by omega]
        exact mul_prod_erase s (fun k => (k : ℤ)) hpj
      have hpQ := (hQ_exact j hj).symm
      have hpair : (j : ℤ) * ((p : ℤ) - j) * ((p : ℤ) * Q j) = (p : ℤ) * P := by
        rw [← hpQ]; nlinarith [h1, h2]
      exact mul_left_cancel₀ (show (p : ℤ) ≠ 0 from by exact_mod_cast hp.ne_zero)
        (by linarith)
    rw [hG_eq, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hP_fact : P = ((p - 1).factorial : ℤ) := by
      show ∏ k ∈ Icc 1 (p - 1), (k : ℤ) = ((p - 1).factorial : ℤ)
      suffices h : ∀ n : ℕ, (Nat.factorial n : ℤ) = ∏ k ∈ Icc 1 n, (k : ℤ) from
        (h _).symm
      intro n; induction n with
      | zero => simp
      | succ m ih =>
        rw [Nat.factorial_succ, Nat.cast_mul, ih,
          show Icc 1 (m + 1) = cons (m + 1) (Icc 1 m) (by simp) from by
            ext x; simp [mem_Icc]; omega,
          prod_cons]
    have hP_wilson : ((P : ℤ) : ZMod p) = -1 := by
      rw [hP_fact]; push_cast; exact ZMod.wilsons_lemma p
    have hj_ne_zero : ∀ j ∈ s, ((j : ℤ) : ZMod p) ≠ 0 := by
      intro j hj
      have hj' := mem_Icc.mp hj
      rw [Ne, Int.cast_natCast, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hdvd; exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    have hQ_zmod : ∀ j ∈ s, ((Q j : ℤ) : ZMod p) = ((j : ℤ) : ZMod p) ^ (p - 3) := by
      intro j hj
      have hj' := mem_Icc.mp hj
      have hrel := hQ_rel j hj
      have hcast : ((j : ℤ) : ZMod p) * (((p : ℤ) - (j : ℤ)) : ZMod p) * ((Q j : ℤ) : ZMod p) =
          ((P : ℤ) : ZMod p) := by
        have := congr_arg (Int.cast : ℤ → ZMod p) hrel
        push_cast at this ⊢; exact this
      have hp_cast : ((p : ℤ) : ZMod p) = 0 := by simp
      rw [show ((p : ℤ) - (j : ℤ) : ZMod p) = -(((j : ℤ) : ZMod p)) from by
        push_cast; simp] at hcast
      rw [hP_wilson] at hcast
      have h1 : ((j : ℤ) : ZMod p) ^ 2 * ((Q j : ℤ) : ZMod p) = 1 := by
        have : -(((j : ℤ) : ZMod p) ^ 2 * ((Q j : ℤ) : ZMod p)) = -1 := by
          have := hcast; ring_nf at this ⊢; exact this
        exact neg_eq_iff_eq_neg.mp this |>.symm ▸ neg_neg 1
      have hj_ne := hj_ne_zero j hj
      have key : ((j : ℤ) : ZMod p) ^ 2 * ((j : ℤ) : ZMod p) ^ (p - 3) = 1 := by
        rw [← pow_add, show 2 + (p - 3) = p - 1 from by omega, Int.cast_natCast]
        exact ZMod.pow_card_sub_one_eq_one (by rwa [Int.cast_natCast] at hj_ne)
      exact mul_left_cancel₀ (pow_ne_zero 2 hj_ne) (h1.trans key.symm)
    rw [Int.cast_sum]
    rw [show (∑ j ∈ s, ((Q j : ℤ) : ZMod p)) = ∑ j ∈ s, ((j : ℤ) : ZMod p) ^ (p - 3) from
      sum_congr rfl hQ_zmod]
    push_cast
    exact sum_pow_Icc_zmod_eq_zero (p - 3) (by omega) (by omega)
  -- Step 5: p² | 2·S₁, then gcd(2,p)=1 gives p² | S₁
  have h_p2_dvd_2S : (p : ℤ) ^ 2 ∣ 2 * ∑ j ∈ s, f j :=
    hG ▸ by rw [sq]; exact mul_dvd_mul_left (p : ℤ) h_p_dvd_G
  exact (by
    exact_mod_cast (by rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd.mpr (fun h =>
      by have := Nat.le_of_dvd (by omega) h; omega) : Nat.Coprime 2 p).isCoprime.pow_right
    : IsCoprime (2 : ℤ) ((p : ℤ) ^ 2)).symm.dvd_of_dvd_mul_left h_p2_dvd_2S

-- ═══════════════════════════════════════════════════════════════
-- §4. Second-order expansion: e₂ recurrence + induction
-- ═══════════════════════════════════════════════════════════════

/-- The second elementary symmetric product of a finite set of naturals. -/
private noncomputable def e2_prod (s : Finset ℕ) : ℤ :=
  ∑ i ∈ s, ∑ j ∈ s.filter (· > i), ∏ k ∈ (s.erase i).erase j, (k : ℤ)

-- --- e2_prod_cons helper lemmas ---

private lemma erase_cons_self_e2 (a : ℕ) (s : Finset ℕ) (ha : a ∉ s) :
    (cons a s ha).erase a = s := by
  simp [cons_eq_insert, erase_insert ha]

private lemma filter_gt_cons_self (a : ℕ) (s : Finset ℕ) (ha : a ∉ s) :
    (cons a s ha).filter (· > a) = s.filter (· > a) := by
  ext x; simp [mem_filter]; omega

private lemma inner_sum_split (a : ℕ) (s : Finset ℕ) (ha : a ∉ s) (i : ℕ) (hi : i ∈ s) :
    ∑ j ∈ (cons a s ha).filter (fun x => x > i),
      ∏ k ∈ ((cons a s ha).erase i).erase j, (k : ℤ) =
    (if i < a then ∏ k ∈ s.erase i, (k : ℤ) else 0) +
    ↑a * ∑ j ∈ s.filter (fun x => x > i),
      ∏ k ∈ (s.erase i).erase j, (k : ℤ) := by
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  have h_erase : (cons a s ha).erase i = insert a (s.erase i) := by
    ext x; simp [mem_erase, mem_cons, mem_insert]
    constructor
    · rintro ⟨hne, rfl | hx⟩ <;> [exact Or.inl rfl; exact Or.inr ⟨hne, hx⟩]
    · rintro (rfl | ⟨hne, hx⟩) <;> [exact ⟨hia.symm, Or.inl rfl⟩; exact ⟨hne, Or.inr hx⟩]
  have ha_not_filter : a ∉ s.filter (fun x => x > i) :=
    fun h => ha (mem_filter.mp h).1
  have ha_erase_i : a ∉ s.erase i :=
    fun h => ha (mem_of_mem_erase h)
  split_ifs with hia_lt
  · have h_filter : (cons a s ha).filter (fun x => x > i) = insert a (s.filter (fun x => x > i)) := by
      ext x; simp only [mem_filter, mem_cons, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hgt⟩ <;> [exact Or.inl rfl; exact Or.inr ⟨hx, hgt⟩]
      · rintro (rfl | ⟨hx, hgt⟩) <;> [exact ⟨Or.inl rfl, hia_lt⟩; exact ⟨Or.inr hx, hgt⟩]
    rw [h_filter, sum_insert ha_not_filter, h_erase]
    congr 1
    · rw [erase_insert ha_erase_i]
    · rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ (mem_filter.mp hj).1)
      rw [erase_insert_of_ne hja.symm]
      rw [prod_insert (fun h => ha (mem_of_mem_erase (mem_of_mem_erase h)))]
  · have h_filter : (cons a s ha).filter (fun x => x > i) = s.filter (fun x => x > i) := by
      ext x; simp only [mem_filter, mem_cons]
      constructor
      · rintro ⟨rfl | hx, hgt⟩
        · exact absurd (Nat.lt_of_lt_of_le hgt (Nat.not_lt.mp hia_lt)) (lt_irrefl _)
        · exact ⟨hx, hgt⟩
      · exact fun ⟨hx, hgt⟩ => ⟨Or.inr hx, hgt⟩
    rw [h_filter, h_erase, zero_add, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hja : j ≠ a := fun h => ha (h ▸ (mem_filter.mp hj).1)
    rw [erase_insert_of_ne hja.symm]
    rw [prod_insert (fun h => ha (mem_of_mem_erase (mem_of_mem_erase h)))]

private lemma sum_filter_partition (a : ℕ) (s : Finset ℕ) (ha : a ∉ s) (f : ℕ → ℤ) :
    ∑ i ∈ s.filter (fun x => a < x), f i +
    ∑ i ∈ s.filter (fun x => x < a), f i =
    ∑ i ∈ s, f i := by
  rw [← sum_filter_add_sum_filter_not s (fun x => a < x)]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext x; simp only [mem_filter, not_lt]
  exact ⟨fun ⟨hx, hlt⟩ => ⟨hx, Nat.le_of_lt_succ (by omega)⟩,
         fun ⟨hx, hle⟩ => ⟨hx, Nat.lt_of_le_of_ne hle (fun h => ha (h ▸ hx))⟩⟩

/-- Recurrence for e₂ when adding an element to a finset. -/
private lemma e2_prod_cons (a : ℕ) (s : Finset ℕ) (ha : a ∉ s) :
    e2_prod (cons a s ha) =
      (∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)) + ↑a * e2_prod s := by
  simp only [e2_prod]
  rw [sum_cons, erase_cons_self_e2 a s ha, filter_gt_cons_self a s ha]
  have h1 : ∑ i ∈ s, ∑ j ∈ (cons a s ha).filter (fun x => x > i),
      ∏ k ∈ ((cons a s ha).erase i).erase j, (k : ℤ) =
    ∑ i ∈ s, ((if i < a then ∏ k ∈ s.erase i, (k : ℤ) else 0) +
    ↑a * ∑ j ∈ s.filter (fun x => x > i),
      ∏ k ∈ (s.erase i).erase j, (k : ℤ)) :=
    sum_congr rfl (fun i hi => inner_sum_split a s ha i hi)
  rw [h1, sum_add_distrib, ← mul_sum]
  have h2 : ∑ i ∈ s, (if i < a then ∏ k ∈ s.erase i, (k : ℤ) else 0) =
      ∑ i ∈ s.filter (fun x => x < a), ∏ k ∈ s.erase i, (k : ℤ) := by
    rw [← sum_filter]
  rw [h2]
  linarith [sum_filter_partition a s ha (fun i => ∏ k ∈ s.erase i, (k : ℤ))]

private lemma sum_prod_erase_cons (a : ℕ) (s : Finset ℕ) (ha : a ∉ s) :
    ∑ j ∈ cons a s ha, ∏ k ∈ (cons a s ha).erase j, (k : ℤ) =
      (∏ k ∈ s, (k : ℤ)) + ↑a * (∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)) := by
  rw [sum_cons, erase_cons ha]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl; intro j hj
  rw [erase_cons_of_ne ha (ne_of_mem_of_not_mem hj ha).symm, prod_cons]

/-- Second-order expansion: ∏(d+aₖ) - ∏aₖ - d·∑∏_{erase j} aₖ = d²·e₂ + d³·T. -/
theorem prod_shift_expansion_2 (s : Finset ℕ) (d : ℤ) :
    ∃ T : ℤ,
      (∏ k ∈ s, (d + (k : ℤ))) - (∏ k ∈ s, (k : ℤ)) -
        d * (∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)) =
        d ^ 2 * e2_prod s + d ^ 3 * T := by
  induction s using cons_induction with
  | empty => exact ⟨0, by simp [e2_prod]⟩
  | cons a s ha ih =>
    obtain ⟨T₀, hT₀⟩ := ih
    set P := ∏ k ∈ s, (k : ℤ)
    set P' := ∏ k ∈ s, (d + (k : ℤ))
    set S₁ := ∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)
    set e₂ := e2_prod s
    refine ⟨e₂ + ↑a * T₀ + d * T₀, ?_⟩
    have hsum := sum_prod_erase_cons a s ha
    have he2 := e2_prod_cons a s ha
    rw [prod_cons, prod_cons, hsum, he2]
    have hP' : P' = P + d * S₁ + d ^ 2 * e₂ + d ^ 3 * T₀ := by linarith
    change (d + ↑a) * P' - ↑a * P - d * (P + ↑a * S₁) =
      d ^ 2 * (S₁ + ↑a * e₂) + d ^ 3 * (e₂ + ↑a * T₀ + d * T₀)
    rw [hP']
    ring

-- ═══════════════════════════════════════════════════════════════
-- §5. p | e₂({1,…,p-1}) — Wilson + Fermat + power sum vanishing
-- ═══════════════════════════════════════════════════════════════

-- Wilson's theorem: ∏_{k=1}^{p-1} k = -1 in ZMod p
private lemma prod_Icc_eq_neg_one {p : Nat} [hp : Fact (Nat.Prime p)] [NeZero p] :
    ∏ k ∈ Icc 1 (p - 1), ((k : ℕ) : ZMod p) = -1 := by
  suffices h : ∀ n : ℕ, (Nat.factorial n : ZMod p) =
      ∏ k ∈ Icc 1 n, ((k : ℕ) : ZMod p) by
    rw [← h]; exact_mod_cast ZMod.wilsons_lemma p
  intro n; induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, ih,
      show Icc 1 (m + 1) = cons (m + 1) (Icc 1 m) (by simp) from by
        ext x; simp [mem_Icc]; omega,
      prod_cons]

private lemma cast_ne_zero {p : Nat} [hp : Fact (Nat.Prime p)] [NeZero p]
    (j : ℕ) (hj : j ∈ Icc 1 (p - 1)) :
    ((j : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdvd
  have hj' := mem_Icc.mp hj
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

-- Key: i * j * ∏_{k≠i,j} k = -1 in ZMod p
private lemma ij_mul_prod_eq_neg_one {p : Nat} [hp : Fact (Nat.Prime p)] [NeZero p]
    (i j : ℕ) (hi : i ∈ Icc 1 (p - 1)) (hj : j ∈ (Icc 1 (p - 1)).filter (· > i)) :
    let s := Icc 1 (p - 1)
    ((i : ℕ) : ZMod p) * ((j : ℕ) : ZMod p) *
      ∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p) = -1 := by
  intro s
  have hj_mem : j ∈ s := (mem_filter.mp hj).1
  have hij : i ≠ j := by
    have := (mem_filter.mp hj).2; omega
  have h1 : ((i : ℕ) : ZMod p) * ∏ k ∈ s.erase i, ((k : ℕ) : ZMod p) =
      ∏ k ∈ s, ((k : ℕ) : ZMod p) :=
    mul_prod_erase s (fun k => ((k : ℕ) : ZMod p)) hi
  have h2 : ((j : ℕ) : ZMod p) * ∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p) =
      ∏ k ∈ s.erase i, ((k : ℕ) : ZMod p) :=
    mul_prod_erase (s.erase i) (fun k => ((k : ℕ) : ZMod p))
      (mem_erase.mpr ⟨hij.symm, hj_mem⟩)
  calc ((i : ℕ) : ZMod p) * ((j : ℕ) : ZMod p) *
        ∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p)
      = ((i : ℕ) : ZMod p) * (((j : ℕ) : ZMod p) *
        ∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p)) := by ring
    _ = ((i : ℕ) : ZMod p) * ∏ k ∈ s.erase i, ((k : ℕ) : ZMod p) := by rw [h2]
    _ = ∏ k ∈ s, ((k : ℕ) : ZMod p) := h1
    _ = -1 := prod_Icc_eq_neg_one

-- ∏_{k≠i,j} k = -i^{p-2} * j^{p-2} in ZMod p
private lemma prod_erase_erase_eq {p : Nat} [hp : Fact (Nat.Prime p)] [NeZero p]
    (i j : ℕ) (hi : i ∈ Icc 1 (p - 1)) (hj : j ∈ (Icc 1 (p - 1)).filter (· > i)) :
    let s := Icc 1 (p - 1)
    (∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p)) =
      -((i : ℕ) : ZMod p) ^ (p - 2) * ((j : ℕ) : ZMod p) ^ (p - 2) := by
  intro s
  have hj_mem : j ∈ s := (mem_filter.mp hj).1
  have hi_ne := cast_ne_zero i hi
  have hj_ne := cast_ne_zero j hj_mem
  have h := ij_mul_prod_eq_neg_one i j hi hj
  have hij_ne : ((i : ℕ) : ZMod p) * ((j : ℕ) : ZMod p) ≠ 0 :=
    mul_ne_zero hi_ne hj_ne
  exact mul_left_cancel₀ hij_ne (show
    ((i : ℕ) : ZMod p) * ((j : ℕ) : ZMod p) *
      (∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p)) =
    ((i : ℕ) : ZMod p) * ((j : ℕ) : ZMod p) *
      (-((i : ℕ) : ZMod p) ^ (p - 2) * ((j : ℕ) : ZMod p) ^ (p - 2)) from by
      rw [h]
      have hi_pow := ZMod.pow_card_sub_one_eq_one hi_ne
      have hj_pow := ZMod.pow_card_sub_one_eq_one hj_ne
      rw [show ((i : ℕ) : ZMod p) * ((j : ℕ) : ZMod p) *
        (-((i : ℕ) : ZMod p) ^ (p - 2) * ((j : ℕ) : ZMod p) ^ (p - 2)) =
        -(((i : ℕ) : ZMod p) ^ (p - 2 + 1) * ((j : ℕ) : ZMod p) ^ (p - 2 + 1)) from by ring]
      rw [show p - 2 + 1 = p - 1 from by have := hp.out.two_le; omega]
      rw [hi_pow, hj_pow]
      ring)

-- Algebraic identity: 2·∑_{i<j} f(i)f(j) = (∑f)² - ∑f²
private lemma two_mul_cross_sum_eq {R : Type*} [CommRing R]
    (s : Finset ℕ) (f : ℕ → R) :
    2 * ∑ i ∈ s, ∑ j ∈ s.filter (· > i), f i * f j =
    (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2 := by
  induction s using cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [sum_cons]
    have h_filter_a : (cons a s ha).filter (· > a) = s.filter (· > a) := by
      ext x; simp only [mem_filter, mem_cons]; constructor
      · rintro ⟨rfl | hx, hgt⟩ <;> [exact absurd hgt (lt_irrefl _); exact ⟨hx, hgt⟩]
      · exact fun ⟨hx, hgt⟩ => ⟨Or.inr hx, hgt⟩
    have h_inner : ∀ i ∈ s, ∑ j ∈ (cons a s ha).filter (· > i), f i * f j =
        (if i < a then f i * f a else 0) +
        ∑ j ∈ s.filter (· > i), f i * f j := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have ha_not : a ∉ s.filter (· > i) := fun h => ha (mem_filter.mp h).1
      split_ifs with hlt
      · have : (cons a s ha).filter (· > i) = insert a (s.filter (· > i)) := by
          ext x; simp only [mem_filter, mem_cons, mem_insert]; constructor
          · rintro ⟨rfl | hx, hgt⟩ <;> [exact Or.inl rfl; exact Or.inr ⟨hx, hgt⟩]
          · rintro (rfl | ⟨hx, hgt⟩) <;> [exact ⟨Or.inl rfl, hlt⟩; exact ⟨Or.inr hx, hgt⟩]
        rw [this, sum_insert ha_not]
      · have : (cons a s ha).filter (· > i) = s.filter (· > i) := by
          ext x; simp only [mem_filter, mem_cons]; constructor
          · rintro ⟨rfl | hx, hgt⟩
            · exfalso; omega
            · exact ⟨hx, hgt⟩
          · exact fun ⟨hx, hgt⟩ => ⟨Or.inr hx, hgt⟩
        rw [this, zero_add]
    rw [sum_congr rfl h_inner, sum_add_distrib, h_filter_a]
    have h_ite : ∑ x ∈ s, (if x < a then f x * f a else 0) =
        ∑ x ∈ s.filter (· < a), f x * f a := by rw [← sum_filter]
    rw [h_ite]
    have h_part : s.filter (· > a) ∪ s.filter (· < a) = s := by
      ext x; simp only [mem_union, mem_filter]; constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx; by_cases h : a < x
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, lt_of_le_of_ne (Nat.le_of_not_lt h) (fun he => ha (he ▸ hx))⟩
    have h_disj : Disjoint (s.filter (· > a)) (s.filter (· < a)) :=
      disjoint_filter.mpr (fun x _ h1 h2 => absurd h1 (not_lt.mpr (Nat.le_of_lt h2)))
    have h_fa : f a * ∑ j ∈ s.filter (· > a), f j +
        ∑ i ∈ s.filter (· < a), f i * f a = f a * ∑ i ∈ s, f i := by
      have : ∑ i ∈ s.filter (· < a), f i * f a =
          f a * ∑ i ∈ s.filter (· < a), f i := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      rw [this, ← mul_add, ← sum_union h_disj, h_part]
    have goal_eq : 2 * (∑ j ∈ s.filter (· > a), f a * f j +
        (∑ x ∈ s.filter (· < a), f x * f a +
         ∑ x ∈ s, ∑ j ∈ s.filter (· > x), f x * f j)) =
      (f a + ∑ i ∈ s, f i) ^ 2 - (f a ^ 2 + ∑ i ∈ s, f i ^ 2) := by
      have : ∑ j ∈ s.filter (· > a), f a * f j = f a * ∑ j ∈ s.filter (· > a), f j := by
        rw [mul_sum]
      rw [this]
      have expand : (f a + ∑ i ∈ s, f i) ^ 2 - (f a ^ 2 + ∑ i ∈ s, f i ^ 2) =
          2 * (f a * ∑ i ∈ s, f i) + ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2) := by ring
      rw [expand, ← ih, ← h_fa]; ring
    simp only [sum_cons]; exact goal_eq

/-- For prime p ≥ 5, p divides e₂({1,…,p-1}). -/
theorem p_dvd_e2_prod (p : Nat) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (p : ℤ) ∣ e2_prod (Icc 1 (p - 1)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set s := Icc 1 (p - 1)
  simp only [e2_prod, Int.cast_sum, Int.cast_prod, Int.cast_natCast]
  have h_rewrite : ∀ i ∈ s, ∀ j ∈ s.filter (· > i),
      (∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p)) =
      -((i : ℕ) : ZMod p) ^ (p - 2) * ((j : ℕ) : ZMod p) ^ (p - 2) :=
    fun i hi j hj => prod_erase_erase_eq i j hi hj
  rw [show ∑ i ∈ s, ∑ j ∈ s.filter (· > i),
      ∏ k ∈ (s.erase i).erase j, ((k : ℕ) : ZMod p) =
    ∑ i ∈ s, ∑ j ∈ s.filter (· > i),
      (-((i : ℕ) : ZMod p) ^ (p - 2) * ((j : ℕ) : ZMod p) ^ (p - 2)) from
    sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => h_rewrite i hi j hj))]
  simp only [neg_mul, sum_neg_distrib]
  rw [neg_eq_zero]
  have h_cross := two_mul_cross_sum_eq s (fun j => ((j : ℕ) : ZMod p) ^ (p - 2))
  have h_sum := sum_pow_Icc_zmod_eq_zero (p - 2) (by omega) (le_refl _)
  have h_sq_sum : ∑ j ∈ s, (((j : ℕ) : ZMod p) ^ (p - 2)) ^ 2 = 0 := by
    have : ∀ j ∈ s, (((j : ℕ) : ZMod p) ^ (p - 2)) ^ 2 =
        ((j : ℕ) : ZMod p) ^ (p - 3) := by
      intro j hj
      rw [← pow_mul, show (p - 2) * 2 = (p - 1) + (p - 3) from by omega,
          pow_add, ZMod.pow_card_sub_one_eq_one (cast_ne_zero j hj), one_mul]
    rw [sum_congr rfl this]
    exact sum_pow_Icc_zmod_eq_zero (p - 3) (by omega) (by omega)
  rw [h_sum, h_sq_sum] at h_cross
  simp at h_cross
  exact h_cross.resolve_left (by
    show ¬((2 : ZMod p) = 0)
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
        CharP.cast_eq_zero_iff (ZMod p) p]
    intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))

-- ═══════════════════════════════════════════════════════════════
-- §6. Product shift mod p³ — connecting all stages
-- ═══════════════════════════════════════════════════════════════

-- First-order expansion: ∏(a+d) - ∏a = d·∑∏_{erase j} a + d²·R
private lemma prod_shift_expansion (s : Finset ℕ) (d : ℤ) :
    ∃ R : ℤ,
      (∏ k ∈ s, (d + (k : ℤ))) - (∏ k ∈ s, (k : ℤ)) =
        d * (∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)) + d ^ 2 * R := by
  induction s using cons_induction with
  | empty => exact ⟨0, by simp⟩
  | cons a s ha ih =>
    obtain ⟨R₀, hR₀⟩ := ih
    set P := ∏ k ∈ s, (k : ℤ)
    set P' := ∏ k ∈ s, (d + (k : ℤ))
    set S := ∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)
    refine ⟨S + ↑a * R₀ + d * R₀, ?_⟩
    have hsum : ∑ j ∈ cons a s ha, ∏ k ∈ (cons a s ha).erase j, (k : ℤ) =
        P + ↑a * S := by
      rw [sum_cons, erase_cons ha]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl; intro j hj
      rw [erase_cons_of_ne ha (ne_of_mem_of_not_mem hj ha).symm, prod_cons]
    rw [prod_cons, prod_cons, hsum]
    have hP' : P' = P + d * S + d ^ 2 * R₀ := by linarith
    calc (d + ↑a) * P' - ↑a * P
        = (d + ↑a) * (P + d * S + d ^ 2 * R₀) - ↑a * P := by rw [hP']
      _ = d * (P + ↑a * S) + d ^ 2 * (S + ↑a * R₀ + d * R₀) := by ring

private lemma prod_shift_mod_cube (p : Nat) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    (↑(p ^ 3) : ℤ) ∣
      (∏ k ∈ Icc 1 (p - 1), ((p : ℤ) + k)) -
      (∏ k ∈ Icc 1 (p - 1), (k : ℤ)) := by
  set s := Icc 1 (p - 1)
  set d : ℤ := ↑p
  obtain ⟨R, hexp⟩ := prod_shift_expansion s d
  set S₁ := ∑ j ∈ s, ∏ k ∈ s.erase j, (k : ℤ)
  -- p² | S₁
  have h_p2_S1 : d ^ 2 ∣ S₁ := harmonic_sum_dvd_sq p hp hp5
  -- p³ | d·S₁
  have h_p3_dS1 : d ^ 3 ∣ d * S₁ := by
    obtain ⟨m, hm⟩ := h_p2_S1; exact ⟨m, by rw [hm]; ring⟩
  rw [hexp]
  suffices h_d_R : d ∣ R by
    obtain ⟨m₁, hm₁⟩ := h_p3_dS1
    obtain ⟨m₂, hm₂⟩ := h_d_R
    refine ⟨m₁ + m₂, ?_⟩
    rw [hm₂, hm₁]; push_cast; ring
  -- p | R via the second-order expansion
  obtain ⟨T, hT⟩ := prod_shift_expansion_2 s d
  have hR_eq : R = e2_prod s + d * T := by
    have h_d2_ne : d ^ 2 ≠ 0 := pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.ne_zero)
    have : d ^ 2 * R = d ^ 2 * (e2_prod s + d * T) := by linarith
    exact mul_left_cancel₀ h_d2_ne this
  have h_dvd_e2 : d ∣ e2_prod s := p_dvd_e2_prod p hp hp5
  have h_dvd_dT : d ∣ d * T := dvd_mul_right d T
  rw [hR_eq]
  exact dvd_add h_dvd_e2 h_dvd_dT

-- ═══════════════════════════════════════════════════════════════
-- §7. Assembly: Wolstenholme's theorem
-- ═══════════════════════════════════════════════════════════════

private lemma _root_.int_dvd_sub_to_nat_mod_w {n m d : ℕ} (hm : m < d) (hn : n ≥ m)
    (h : (d : ℤ) ∣ (↑n - ↑m)) : n % d = m := by
  have hnat : d ∣ (n - m) := by
    rw [Int.natCast_dvd_natCast.symm]; rwa [Nat.cast_sub hn]
  obtain ⟨k, hk⟩ := hnat
  rw [show n = m + d * k from by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

private lemma coprime_cube_factorial (p : Nat) (hp : Nat.Prime p) :
    Nat.Coprime (p ^ 3) ((p - 1).factorial) := by
  apply Nat.Coprime.pow_left
  rw [hp.coprime_iff_not_dvd]; intro h; rw [hp.dvd_factorial] at h
  exact Nat.lt_irrefl p (lt_of_le_of_lt h (Nat.sub_lt hp.pos Nat.one_pos))

private lemma choose_double_eq (p : Nat) (hp : p ≥ 1) :
    Nat.choose (2 * p) p = 2 * Nat.choose (2 * p - 1) (p - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simp only [Nat.succ_sub_one, show 2 * (m + 1) = (2 * m + 1) + 1 from by omega]
  rw [Nat.choose_succ_succ]
  have : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    have h := Nat.choose_symm (show m ≤ 2 * m + 1 by omega)
    rw [show (2 * m + 1) - m = m + 1 from by omega] at h; exact h
  rw [this]; ring

private lemma choose_mul_factorial_eq_prod (p : Nat) (hp : p ≥ 1) :
    (Nat.choose (2 * p - 1) (p - 1) : ℤ) * ↑((p - 1).factorial) =
      ∏ k ∈ Icc 1 (p - 1), ((p : ℤ) + k) := by
  rw [show (Nat.choose (2 * p - 1) (p - 1) : ℤ) * ↑((p - 1).factorial) =
      ↑(Nat.descFactorial (2 * p - 1) (p - 1)) from by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring]
  rw [Nat.descFactorial_eq_prod_range]; push_cast
  apply prod_nbij (fun i => p - 1 - i)
  · intro a ha; simp at ha; simp; omega
  · intro a₁ ha₁ a₂ ha₂ h; simp at ha₁ ha₂; dsimp at h; omega
  · intro c hc; simp at hc; exact ⟨p - 1 - c, by simp; omega, by dsimp; omega⟩
  · intro a ha; simp at ha; dsimp
    rw [Nat.cast_sub (by omega : a ≤ 2 * p - 1)]; push_cast; omega

private lemma factorial_eq_prod_Icc (n : Nat) :
    (n.factorial : ℤ) = ∏ k ∈ Icc 1 n, (k : ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, ih,
      show Icc 1 (m + 1) = cons (m + 1) (Icc 1 m) (by simp) from by
        ext x; simp [mem_Icc]; omega,
      prod_cons]

/-- **Wolstenholme's theorem**: C(2p, p) ≡ 2 (mod p³) for prime p ≥ 5. -/
theorem wolstenholme_binom (p : Nat) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
    Nat.choose (2 * p) p % (p ^ 3) = 2 := by
  have hpge : p ≥ 1 := by omega
  have heq := choose_double_eq p hpge
  have hdvd_prod : (↑(p ^ 3) : ℤ) ∣
      (↑(Nat.choose (2*p-1) (p-1)) - 1) * ↑((p-1).factorial) := by
    rw [sub_one_mul, choose_mul_factorial_eq_prod p hpge, factorial_eq_prod_Icc (p - 1)]
    exact prod_shift_mod_cube p hp hp5
  have hdvd_choose : (↑(p ^ 3) : ℤ) ∣ (↑(Nat.choose (2*p-1) (p-1)) - 1) :=
    (coprime_cube_factorial p hp).isCoprime.dvd_of_dvd_mul_right hdvd_prod
  have hdvd_final : (↑(p ^ 3) : ℤ) ∣ (↑(Nat.choose (2*p) p) - 2) := by
    push_cast [heq]
    rw [show (2 : ℤ) * ↑(Nat.choose (2*p-1) (p-1)) - 2 =
           2 * (↑(Nat.choose (2*p-1) (p-1)) - 1) from by ring]
    exact dvd_mul_of_dvd_right hdvd_choose 2
  exact int_dvd_sub_to_nat_mod_w
    (by have := hp.one_lt; nlinarith [sq_nonneg p])
    (by rw [heq]; have := Nat.choose_pos (show p - 1 ≤ 2 * p - 1 by omega); omega)
    hdvd_final
