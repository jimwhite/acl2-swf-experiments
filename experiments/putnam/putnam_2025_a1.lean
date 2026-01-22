import Mathlib
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
open Classical

theorem putnam_2025_a1 (m n : ℕ → ℕ)
  (h0 : m 0 > 0 ∧ n 0 > 0 ∧ m 0 ≠ n 0)
  (hm : ∀ k : ℕ, m (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).num)
  (hn : ∀ k : ℕ, n (k + 1) = ((2 * m k + 1) / (2 * n k + 1) : ℚ).den):
  {k | ¬ (2 * m k + 1).Coprime (2 * n k + 1)}.Finite := by

  -- First, prove m(k) ≠ n(k) for all k
  have hne : ∀ k, m k ≠ n k := by
    intro k
    induction k with
    | zero => exact h0.2.2
    | succ k ih =>
      intro heq
      have hm' := hm k
      have hn' := hn k
      have heq' : (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).num =
                  (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).den := by
        rw [← hm', ← hn']
        simp only [heq]
      have hpos : (0 : ℚ) < (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1) := by
        apply div_pos
        · have : (0 : ℚ) ≤ m k := Nat.cast_nonneg (m k)
          linarith
        · have : (0 : ℚ) ≤ n k := Nat.cast_nonneg (n k)
          linarith
      have hone : (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1) = 1 := by
        have hthis : ((2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1)).num =
                     ((2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1)).den := heq'
        have hnum_pos : 0 < ((2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1)).num := by
          rw [Rat.num_pos]
          exact hpos
        rw [Rat.eq_iff_mul_eq_mul]
        simp only [Rat.num_one, Rat.den_one, one_mul, Nat.cast_one, mul_one]
        rw [hthis]
      have hmn_eq : (2 * (m k : ℚ) + 1) = (2 * (n k : ℚ) + 1) := by
        field_simp at hone
        have : (0 : ℚ) ≤ n k := Nat.cast_nonneg (n k)
        linarith
      have hmk_eq_nk : (m k : ℚ) = n k := by linarith
      have : m k = n k := Nat.cast_injective hmk_eq_nk
      exact ih this

  -- Define the absolute difference function
  let D : ℕ → ℕ := fun k => if m k ≥ n k then m k - n k else n k - m k

  -- D(k) ≥ 1 for all k (since m k ≠ n k)
  have hD_pos : ∀ k, D k ≥ 1 := by
    intro k
    simp only [D]
    split_ifs with h
    · have hlt : n k < m k := Nat.lt_of_le_of_ne h (fun heq => hne k heq.symm)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt)
    · push_neg at h
      exact Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt h)

  have hD_bound : D 0 ≤ m 0 + n 0 := by
    simp only [D]
    split_ifs <;> omega

  -- Define the gcd function
  let g : ℕ → ℕ := fun k => (2 * m k + 1).gcd (2 * n k + 1)

  -- Each gcd is odd (since 2m+1 and 2n+1 are both odd)
  have hg_odd : ∀ k, Odd (g k) := by
    intro k
    simp only [g]
    have h1 : Odd (2 * m k + 1) := ⟨m k, by ring⟩
    have h1_cop : (2 * m k + 1).Coprime 2 := h1.coprime_two_right
    have h_gcd_cop := Nat.Coprime.gcd_left (2 * n k + 1) h1_cop
    rw [Nat.gcd_comm]
    exact (Nat.Coprime.symm h_gcd_cop).odd_of_left

  -- At a bad step, gcd ≥ 3
  have hg_ge3 : ∀ k, ¬(2 * m k + 1).Coprime (2 * n k + 1) → g k ≥ 3 := by
    intro k hbad
    simp only [g]
    have hodd := hg_odd k
    simp only [g] at hodd
    have hne1 : (2 * m k + 1).gcd (2 * n k + 1) ≠ 1 := by
      intro h
      exact hbad h
    have hpos : (2 * m k + 1).gcd (2 * n k + 1) > 0 :=
      Nat.gcd_pos_of_pos_left _ (by omega : 2 * m k + 1 > 0)
    obtain ⟨r, hr⟩ := hodd
    omega

  -- gcd(2m+1, 2n+1) | D
  have hg_dvd_D : ∀ k, g k ∣ D k := by
    intro k
    simp only [g, D]
    have hgcd1 := Nat.gcd_dvd_left (2 * m k + 1) (2 * n k + 1)
    have hgcd2 := Nat.gcd_dvd_right (2 * m k + 1) (2 * n k + 1)
    split_ifs with hmn
    · have hdiff : (2 * m k + 1) - (2 * n k + 1) = 2 * (m k - n k) := by omega
      have hdvd_diff : (2 * m k + 1).gcd (2 * n k + 1) ∣ (2 * m k + 1) - (2 * n k + 1) :=
        Nat.dvd_sub hgcd1 hgcd2
      rw [hdiff] at hdvd_diff
      have hodd := hg_odd k
      simp only [g] at hodd
      have hcop2 : ((2 * m k + 1).gcd (2 * n k + 1)).Coprime 2 := hodd.coprime_two_right
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd_diff
    · push_neg at hmn
      have hdiff : (2 * n k + 1) - (2 * m k + 1) = 2 * (n k - m k) := by omega
      have hdvd_diff : (2 * m k + 1).gcd (2 * n k + 1) ∣ (2 * n k + 1) - (2 * m k + 1) :=
        Nat.dvd_sub hgcd2 hgcd1
      rw [hdiff] at hdvd_diff
      have hodd := hg_odd k
      simp only [g] at hodd
      have hcop2 : ((2 * m k + 1).gcd (2 * n k + 1)).Coprime 2 := hodd.coprime_two_right
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd_diff

  -- Define the bad set
  let S := {k | ¬(2 * m k + 1).Coprime (2 * n k + 1)}

  -- Use contradiction argument
  by_contra hinf
  push_neg at hinf
  have hSinf : S.Infinite := hinf

  -- Get D 0 + 1 distinct bad indices
  let f := Set.Infinite.natEmbedding S hSinf

  -- These give D 0 + 1 elements
  let indices : Finset ℕ := Finset.image (fun i : Fin (D 0 + 1) => (f i).val) Finset.univ

  have hcard : indices.card = D 0 + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij
      have : (f i).val = (f j).val := hij
      have : f i = f j := Subtype.ext this
      exact Fin.ext (f.injective this)

  have hin_bad : ∀ i ∈ indices, ¬(2 * m i + 1).Coprime (2 * n i + 1) := by
    intro i hi
    simp only [indices, Finset.mem_image, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hj⟩ := hi
    rw [← hj]
    exact (f j).property

  -- Each g(i) ≥ 3 for i ∈ indices
  have hg_ge3' : ∀ i ∈ indices, g i ≥ 3 := fun i hi => hg_ge3 i (hin_bad i hi)

  -- The product ∏_{i ∈ indices} g(i) ≥ 3^{D 0 + 1}
  have hprod_ge : 3 ^ (D 0 + 1) ≤ indices.prod g := by
    calc 3 ^ (D 0 + 1) = 3 ^ indices.card := by rw [hcard]
      _ = indices.prod (fun _ => 3) := by
          rw [Finset.prod_const, hcard]
      _ ≤ indices.prod g := by
          apply Finset.prod_le_prod
          · intro i _; omega
          · exact hg_ge3'

  -- Now 3^{D 0 + 1} > D 0
  have h3pow : 3 ^ (D 0 + 1) > D 0 := by
    have hD0ge1 : D 0 ≥ 1 := hD_pos 0
    have h : D 0 + 1 < 3 ^ (D 0 + 1) := @Nat.lt_pow_self (D 0 + 1) 3 (by omega : 1 < 3)
    omega

  have hprod_gt_D0 : indices.prod g > D 0 := lt_of_lt_of_le h3pow hprod_ge

  -- Key: g(k) * m(k+1) = 2*m(k)+1
  -- This follows from the rational number representation: the numerator of a/b in reduced form
  -- is a/gcd(a,b), so gcd(a,b) * (a/gcd(a,b)) = a
  have hm_rec : ∀ k, g k * m (k + 1) = 2 * m k + 1 := by
    intro k
    simp only [g]
    have h_gk_dvd : (2 * m k + 1).gcd (2 * n k + 1) ∣ (2 * m k + 1) := Nat.gcd_dvd_left _ _
    have hmk1 : (m (k + 1) : ℤ) = (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).num := hm k
    have hqk_pos : (0 : ℚ) < (2 * (m k : ℚ) + 1) / (2 * (n k : ℚ) + 1) := by
      apply div_pos <;> positivity
    have hnum_nonneg : 0 ≤ (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).num := by
      rw [Rat.num_nonneg]; exact le_of_lt hqk_pos
    have hmk1_nat : m (k + 1) = (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).num.toNat := by
      have h := hmk1; omega
    have h2m1 : (2 * (m k : ℚ) + 1) = ((2 * m k + 1 : ℕ) : ℚ) := by push_cast; ring
    have h2n1 : (2 * (n k : ℚ) + 1) = ((2 * n k + 1 : ℕ) : ℚ) := by push_cast; ring
    have hne : (2 * n k + 1 : ℕ) ≠ 0 := by omega
    have hm_pos : (2 * m k + 1 : ℕ) > 0 := by omega
    have hn_pos : (2 * n k + 1 : ℕ) > 0 := by omega
    -- The key insight: for positive coprime p, q, (p/q).num = p and (p/q).den = q
    -- For non-coprime, (p/q).num = p/gcd and (p/q).den = q/gcd
    have hgcd_eq : (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).num.toNat =
                   (2 * m k + 1) / (2 * m k + 1).gcd (2 * n k + 1) := by
      rw [h2m1, h2n1]
      have hdiv_rat : ((2 * m k + 1 : ℕ) : ℚ) / ((2 * n k + 1 : ℕ) : ℚ) =
                      Rat.divInt (2 * m k + 1 : ℤ) (2 * n k + 1 : ℤ) := by
        rw [Rat.divInt_eq_div]; push_cast; rfl
      rw [hdiv_rat]
      -- Use Rat.num_divInt: (Rat.divInt a b).num = b.sign * a / ↑(b.gcd a)
      have h_pos_n : (0 : ℤ) < (2 * n k + 1 : ℤ) := by omega
      have h_sign : (2 * n k + 1 : ℤ).sign = 1 := Int.sign_eq_one_of_pos h_pos_n
      have hnum : (Rat.divInt (2 * m k + 1 : ℤ) (2 * n k + 1 : ℤ)).num =
                  (2 * m k + 1 : ℤ) / ((2 * n k + 1 : ℤ).gcd (2 * m k + 1)) := by
        rw [Rat.num_divInt, h_sign, one_mul]
      have hnum_pos : 0 ≤ (Rat.divInt (2 * m k + 1 : ℤ) (2 * n k + 1 : ℤ)).num := by
        rw [Rat.num_nonneg]
        rw [Rat.divInt_nonneg_iff_of_pos_right h_pos_n]
        omega
      have hgcd_comm : (2 * n k + 1 : ℤ).gcd (2 * m k + 1) = (2 * m k + 1 : ℤ).gcd (2 * n k + 1) :=
        Int.gcd_comm _ _
      have hgcd_nat : (2 * m k + 1 : ℤ).gcd (2 * n k + 1) = ((2 * m k + 1).gcd (2 * n k + 1) : ℕ) :=
        Int.gcd_natCast_natCast _ _
      rw [hnum, hgcd_comm, hgcd_nat]
      have h2m_nat : ((2 : ℤ) * (m k : ℤ) + 1) = ((2 * m k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h2m_nat]
      rw [← Int.natCast_div, Int.toNat_natCast]
    rw [hmk1_nat, hgcd_eq]
    exact Nat.mul_div_cancel' h_gk_dvd

  -- Similarly: g(k) * n(k+1) = 2*n(k)+1
  have hn_rec : ∀ k, g k * n (k + 1) = 2 * n k + 1 := by
    intro k
    simp only [g]
    have h_gk_dvd : (2 * m k + 1).gcd (2 * n k + 1) ∣ (2 * n k + 1) := Nat.gcd_dvd_right _ _
    have hnk1 : n (k + 1) = (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).den := hn k
    have h2m1 : (2 * (m k : ℚ) + 1) = ((2 * m k + 1 : ℕ) : ℚ) := by push_cast; ring
    have h2n1 : (2 * (n k : ℚ) + 1) = ((2 * n k + 1 : ℕ) : ℚ) := by push_cast; ring
    have hne : (2 * n k + 1 : ℕ) ≠ 0 := by omega
    have hm_pos : (2 * m k + 1 : ℕ) > 0 := by omega
    have hn_pos : (2 * n k + 1 : ℕ) > 0 := by omega
    have hgcd_eq : (((2 : ℚ) * (m k) + 1) / ((2 : ℚ) * (n k) + 1)).den =
                   (2 * n k + 1) / (2 * m k + 1).gcd (2 * n k + 1) := by
      rw [h2m1, h2n1]
      have hdiv_rat : ((2 * m k + 1 : ℕ) : ℚ) / ((2 * n k + 1 : ℕ) : ℚ) =
                      Rat.divInt (2 * m k + 1 : ℤ) (2 * n k + 1 : ℤ) := by
        rw [Rat.divInt_eq_div]; push_cast; rfl
      rw [hdiv_rat]
      -- Use Rat.den_divInt: (Rat.divInt a b).den = if b = 0 then 1 else b.natAbs / b.gcd a
      have hne_int : (2 * n k + 1 : ℤ) ≠ 0 := by omega
      have hden : (Rat.divInt (2 * m k + 1 : ℤ) (2 * n k + 1 : ℤ)).den =
                  (2 * n k + 1 : ℤ).natAbs / (2 * n k + 1 : ℤ).gcd (2 * m k + 1) := by
        rw [Rat.den_divInt]
        simp only [hne_int, ↓reduceIte]
      rw [hden]
      have hgcd_comm : (2 * n k + 1 : ℤ).gcd (2 * m k + 1) = (2 * m k + 1 : ℤ).gcd (2 * n k + 1) :=
        Int.gcd_comm _ _
      have hgcd_nat : (2 * m k + 1 : ℤ).gcd (2 * n k + 1) = ((2 * m k + 1).gcd (2 * n k + 1) : ℕ) :=
        Int.gcd_natCast_natCast _ _
      rw [hgcd_comm, hgcd_nat, Nat.gcd_comm]
      have h2n_nat : ((2 : ℤ) * (n k : ℤ) + 1).natAbs = (2 * n k + 1 : ℕ) := by
        rw [show ((2 : ℤ) * (n k : ℤ) + 1) = ((2 * n k + 1 : ℕ) : ℤ) from by push_cast; ring]
        exact Int.natAbs_natCast _
      rw [h2n_nat]
    rw [hnk1, hgcd_eq]
    exact Nat.mul_div_cancel' h_gk_dvd

  -- Now the recurrence for D: D(k+1) * g(k) = 2 * D(k)
  have hD_rec : ∀ k, D (k + 1) * g k = 2 * D k := by
    intro k
    simp only [D]
    have hmn_rec := hm_rec k
    have hnn_rec := hn_rec k
    have h_gk_pos : g k > 0 := by
      simp only [g]
      exact Nat.gcd_pos_of_pos_left _ (by omega : 2 * m k + 1 > 0)
    by_cases hmn : m k ≥ n k
    · -- m k ≥ n k case
      simp only [if_pos hmn]
      have h_mk1_ge_nk1 : m (k + 1) ≥ n (k + 1) := by
        have h1 : g k * m (k + 1) ≥ g k * n (k + 1) := by rw [hmn_rec, hnn_rec]; omega
        exact Nat.le_of_mul_le_mul_left h1 h_gk_pos
      simp only [if_pos h_mk1_ge_nk1]
      have h1 : g k * m (k + 1) - g k * n (k + 1) = 2 * m k + 1 - (2 * n k + 1) := by
        rw [hmn_rec, hnn_rec]
      have h2 : 2 * m k + 1 - (2 * n k + 1) = 2 * (m k - n k) := by omega
      calc (m (k + 1) - n (k + 1)) * g k
          = g k * m (k + 1) - g k * n (k + 1) := by
            have : g k * (m (k + 1) - n (k + 1)) = g k * m (k + 1) - g k * n (k + 1) := Nat.mul_sub _ _ _
            linarith [this]
          _ = 2 * m k + 1 - (2 * n k + 1) := h1
          _ = 2 * (m k - n k) := h2
    · -- n k > m k case
      push_neg at hmn
      simp only [if_neg (by omega : ¬(m k ≥ n k))]
      have h_nk1_ge_mk1 : n (k + 1) ≥ m (k + 1) := by
        have h1 : g k * n (k + 1) ≥ g k * m (k + 1) := by rw [hmn_rec, hnn_rec]; omega
        exact Nat.le_of_mul_le_mul_left h1 h_gk_pos
      have h_neg : ¬(m (k + 1) ≥ n (k + 1)) := by
        intro hge
        have heq : m (k + 1) = n (k + 1) := le_antisymm h_nk1_ge_mk1 hge
        exact hne (k + 1) heq
      simp only [if_neg h_neg]
      have h1 : g k * n (k + 1) - g k * m (k + 1) = 2 * n k + 1 - (2 * m k + 1) := by
        rw [hmn_rec, hnn_rec]
      have h2 : 2 * n k + 1 - (2 * m k + 1) = 2 * (n k - m k) := by omega
      calc (n (k + 1) - m (k + 1)) * g k
          = g k * n (k + 1) - g k * m (k + 1) := by
            have : g k * (n (k + 1) - m (k + 1)) = g k * n (k + 1) - g k * m (k + 1) := Nat.mul_sub _ _ _
            linarith [this]
          _ = 2 * n k + 1 - (2 * m k + 1) := h1
          _ = 2 * (n k - m k) := h2

  -- Product formula: D(K) * ∏_{i<K} g(i) = 2^K * D(0)
  have hprod_formula : ∀ K, D K * (Finset.range K).prod g = 2^K * D 0 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.range_add_one, Finset.prod_insert Finset.notMem_range_self]
      calc D (K + 1) * (g K * (Finset.range K).prod g)
          = (D (K + 1) * g K) * (Finset.range K).prod g := by ring
        _ = (2 * D K) * (Finset.range K).prod g := by rw [hD_rec K]
        _ = 2 * (D K * (Finset.range K).prod g) := by ring
        _ = 2 * (2^K * D 0) := by rw [ih]
        _ = 2^(K+1) * D 0 := by ring

  -- Define oddPart
  let oddPart : ℕ → ℕ := fun n => n / 2 ^ n.factorization 2

  -- Key helper: odd g divides d implies g divides oddPart d
  have h_odd_dvd_oddPart : ∀ d g : ℕ, d > 0 → Odd g → g ∣ d → g ∣ oddPart d := by
    intro d g' hd_pos hg_odd hg_dvd
    simp only [oddPart]
    have hv : 2 ^ d.factorization 2 ∣ d := Nat.ordProj_dvd d 2
    have hdiv : d / 2 ^ d.factorization 2 * 2 ^ d.factorization 2 = d := Nat.div_mul_cancel hv
    have hg_cop_2v : g'.Coprime (2 ^ d.factorization 2) := by
      apply Nat.Coprime.pow_right
      exact hg_odd.coprime_two_right
    rw [← hdiv] at hg_dvd
    exact Nat.Coprime.dvd_of_dvd_mul_right hg_cop_2v hg_dvd

  -- oddPart formula by induction: oddPart(D(K)) * ∏_{i<K} g(i) = oddPart(D(0))
  have hoddPart_descent : ∀ K, oddPart (D K) * (Finset.range K).prod g = oddPart (D 0) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.range_add_one, Finset.prod_insert Finset.notMem_range_self]
      have h_gK_dvd : g K ∣ D K := hg_dvd_D K
      have h_gK_odd : Odd (g K) := hg_odd K
      have h_DK_pos : D K > 0 := hD_pos K
      have h_gK_dvd_op : g K ∣ oddPart (D K) := h_odd_dvd_oddPart (D K) (g K) h_DK_pos h_gK_odd h_gK_dvd
      have h_gK_pos : g K > 0 := by
        simp only [g]
        exact Nat.gcd_pos_of_pos_left _ (by omega : 2 * m K + 1 > 0)

      -- Key: oddPart(D(K+1)) * g(K) = oddPart(D(K))
      -- D(K+1) = 2 * D(K) / g(K), and g(K) divides oddPart(D(K))
      -- So oddPart(D(K+1)) = oddPart(D(K)) / g(K)
      have h_prod : oddPart (D (K + 1)) * g K = oddPart (D K) := by
        -- D(K+1) * g(K) = 2 * D(K)
        have h_DK1 : D (K + 1) * g K = 2 * D K := hD_rec K
        -- D(K) = 2^a * oddPart(D(K)) where a = factorization 2
        let a := (D K).factorization 2
        have h_factor : D K = 2 ^ a * oddPart (D K) := by
          simp only [a, oddPart]
          exact (Nat.ordProj_mul_ordCompl_eq_self (D K) 2).symm
        -- 2 * D(K) = 2^{a+1} * oddPart(D(K))
        have h_2DK : 2 * D K = 2 ^ (a + 1) * oddPart (D K) := by
          conv_lhs => rw [h_factor]
          rw [pow_succ', mul_assoc]
        -- D(K+1) = 2^{a+1} * oddPart(D(K)) / g(K)
        -- g(K) | oddPart(D(K)), so D(K+1) = 2^{a+1} * (oddPart(D(K)) / g(K))
        have h_gK_dvd_2D : g K ∣ 2 * D K := Dvd.dvd.mul_left h_gK_dvd 2
        have h_DK1_eq : D (K + 1) = 2 * D K / g K := by
          have heq : 2 * D K = g K * D (K + 1) := by
            rw [mul_comm (g K), h_DK1]
          exact (Nat.div_eq_of_eq_mul_right h_gK_pos heq).symm
        rw [h_DK1_eq, h_2DK]
        -- 2^{a+1} * oddPart(D(K)) / g(K) = 2^{a+1} * (oddPart(D(K)) / g(K))
        have h1 : 2 ^ (a + 1) * oddPart (D K) / g K = 2 ^ (a + 1) * (oddPart (D K) / g K) := by
          rw [Nat.mul_div_assoc _ h_gK_dvd_op]
        rw [h1]
        -- oddPart(2^{a+1} * r) = r when r is odd (and r = oddPart(D(K)) / g(K))
        have h_DK_ne_zero : D K ≠ 0 := Nat.pos_iff_ne_zero.mp h_DK_pos
        have h_r_pos : oddPart (D K) / g K > 0 := by
          apply Nat.div_pos
          · exact Nat.le_of_dvd (Nat.ordCompl_pos 2 h_DK_ne_zero) h_gK_dvd_op
          · exact h_gK_pos
        -- r = oddPart(D(K)) / g(K) is odd
        have h_r_odd : Odd (oddPart (D K) / g K) := by
          have h_op_odd : Odd (oddPart (D K)) := by
            simp only [oddPart]
            exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two h_DK_ne_zero)
          exact Odd.of_dvd_nat h_op_odd ⟨g K, (Nat.div_mul_cancel h_gK_dvd_op).symm⟩
        -- oddPart(2^{a+1} * r) = r
        have h_op_eq : oddPart (2 ^ (a + 1) * (oddPart (D K) / g K)) = oddPart (D K) / g K := by
          simp only [oddPart]
          have h_r := oddPart (D K) / g K
          -- factorization 2 of 2^{a+1} * r = a+1 when r is odd
          have h_fact : (2 ^ (a + 1) * (oddPart (D K) / g K)).factorization 2 = a + 1 := by
            rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (Nat.pos_iff_ne_zero.mp h_r_pos)]
            rw [Nat.Prime.factorization_pow Nat.prime_two]
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
            have h_odd_fact : (oddPart (D K) / g K).factorization 2 = 0 := by
              rw [Nat.factorization_eq_zero_of_not_dvd]
              exact h_r_odd.not_two_dvd_nat
            omega
          calc (2 ^ (a + 1) * (oddPart (D K) / g K)) /
                2 ^ (2 ^ (a + 1) * (oddPart (D K) / g K)).factorization 2
              = (2 ^ (a + 1) * (oddPart (D K) / g K)) / 2 ^ (a + 1) := by rw [h_fact]
            _ = oddPart (D K) / g K := Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)
        rw [h_op_eq]
        exact Nat.div_mul_cancel h_gK_dvd_op

      calc oddPart (D (K + 1)) * (g K * (Finset.range K).prod g)
          = (oddPart (D (K + 1)) * g K) * (Finset.range K).prod g := by ring
        _ = oddPart (D K) * (Finset.range K).prod g := by rw [h_prod]
        _ = oddPart (D 0) := ih

  -- Now the bound: ∏_{i<K} g(i) ≤ oddPart(D(0)) ≤ D(0)
  have hprod_bound : ∀ K, (Finset.range K).prod g ≤ D 0 := by
    intro K
    have h_D0_ne_zero : D 0 ≠ 0 := Nat.pos_iff_ne_zero.mp (hD_pos 0)
    have h_DK_ne_zero : D K ≠ 0 := Nat.pos_iff_ne_zero.mp (hD_pos K)
    have h_op_pos : oddPart (D 0) > 0 := Nat.ordCompl_pos 2 h_D0_ne_zero
    have h_opK_pos : oddPart (D K) > 0 := Nat.ordCompl_pos 2 h_DK_ne_zero
    have h_from_descent := hoddPart_descent K
    have h_prod_eq : (Finset.range K).prod g = oddPart (D 0) / oddPart (D K) := by
      have h := h_from_descent
      have h_dvd : oddPart (D K) ∣ oddPart (D 0) := ⟨(Finset.range K).prod g, h.symm⟩
      have heq : oddPart (D 0) = oddPart (D K) * (Finset.range K).prod g := h.symm
      exact (Nat.div_eq_of_eq_mul_right h_opK_pos heq).symm
    rw [h_prod_eq]
    calc oddPart (D 0) / oddPart (D K) ≤ oddPart (D 0) := Nat.div_le_self _ _
      _ ≤ D 0 := Nat.ordCompl_le (D 0) 2

  -- Now show: indices.prod g ≤ D 0
  -- indices ⊆ range K for large enough K
  let K := indices.sup id + 1
  have h_indices_in_range : indices ⊆ Finset.range K := by
    simp only [K]
    exact Finset.subset_range_sup_succ indices

  have h_indices_prod_le : indices.prod g ≤ (Finset.range K).prod g := by
    apply Finset.prod_le_prod_of_subset_of_one_le' h_indices_in_range
    intro i _ _
    exact Nat.one_le_iff_ne_zero.mpr (Nat.gcd_pos_of_pos_left _ (by omega : 2 * m i + 1 > 0)).ne'

  have h_final : indices.prod g ≤ D 0 := le_trans h_indices_prod_le (hprod_bound K)

  -- But indices.prod g ≥ 3^{D 0 + 1} > D 0
  -- This contradicts h_final
  have hcontra : indices.prod g > D 0 := lt_of_lt_of_le h3pow hprod_ge
  omega


#print axioms putnam_2025_a1
