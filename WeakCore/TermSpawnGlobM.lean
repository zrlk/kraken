import WeakCore.TermSpawnMid
/-!
# TermSpawnGlobM — the memory/resource global `SysInvN` clauses of a mid-run spawn

`c' = spawnT c i par kid`, `Eg' = EgK Eg c`, totals/credits extended by zero at the kid's
index `n = c.ths.size` (`extZ`/`extZT`).  The parent (index `i`) and the kid hold no promises.
-/
namespace TermSpawnGlobM
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermSpawnMid
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section sums
variable {c : Cfg} {i : Nat} {th par kid : TTh}

/-- Off the kid, a spawned configuration's promise sums are the old ones. -/
theorem pSumAt_spawnT_lt (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises)
    {j : Nat} (hj : j < c.ths.size) (f : Ts → Res) : pSumAt (spawnT c i par kid) j f = pSumAt c j f := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  by_cases hji : j = i
  · subst hji
    unfold pSumAt; rw [spawnT_get_par hi, hth]
    simp only [pSum, stOf, hpp]
  · exact TermBal.pSumAt_eq (spawnT_get_ne hji (Nat.ne_of_lt hj)) f

/-- The kid's promise sum is zero. -/
theorem pSumAt_spawnT_kid (hkp : kid.promises = []) (f : Ts → Res) :
    pSumAt (spawnT c i par kid) c.ths.size f = .zero := by
  unfold pSumAt; rw [spawnT_get_kid]; simp only [pSum, stOf, hkp]; rfl

/-- A `Res` sum over one more index, zero there. -/
theorem rsum_ext {n : Nat} {f g : Nat → Res} (hf : ∀ j, j < n → f j = g j) (hn : f n = .zero) :
    Res.sum ((List.range (n + 1)).map f) = Res.sum ((List.range n).map g) := by
  rw [List.range_succ, List.map_append, Res.sum_append, List.map_congr_left (fun j hj => hf j (List.mem_range.1 hj))]
  simp [hn]

/-- A `Nat` sum over one more index, zero there. -/
theorem nsum_ext {n : Nat} {f g : Nat → Nat} (hf : ∀ j, j < n → f j = g j) (hn : f n = 0) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map g).sum := by
  rw [List.range_succ, List.map_append, List.sum_append, List.map_congr_left (fun j hj => hf j (List.mem_range.1 hj))]
  simp [hn]

theorem extZ_lt {F : Nat → Res} {n j : Nat} (h : j < n) : extZ F n j = F j := by
  simp [extZ, Nat.ne_of_lt h]

theorem extZT_lt {F : Nat → Ts → Res} {n j : Nat} (h : j < n) : extZT F n j = F j := by
  simp [extZT, Nat.ne_of_lt h]

@[simp] theorem extZ_self (F : Nat → Res) (n : Nat) : extZ F n n = .zero := by simp [extZ]
@[simp] theorem extZT_self (F : Nat → Ts → Res) (n : Nat) : extZT F n n = fun _ => .zero := by simp [extZT]

variable (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises) (hkp : kid.promises = [])
include hth hpp hkp

/-- The balance sum (totals, credits, held) after the spawn. -/
theorem thSum_bal_spawnT (Tot HP : Nat → Res) (cr : Nat → Ts → Res) :
    thSum (spawnT c i par kid).ths.size
        (fun j => extZ Tot c.ths.size j + pSumAt (spawnT c i par kid) j (extZT cr c.ths.size j) + extZ HP c.ths.size j) =
      thSum c.ths.size (fun j => Tot j + pSumAt c j (cr j) + HP j) := by
  unfold thSum; rw [spawnT_size]
  refine rsum_ext (fun j hj => ?_) ?_
  · rw [extZ_lt hj, extZ_lt hj, extZT_lt hj, pSumAt_spawnT_lt hth hpp hj]
  · simp only [extZ_self, extZT_self, pSumAt_spawnT_kid hkp]; rfl

/-- The debit sum after the spawn. -/
theorem thSum_db_spawnT (db : Nat → Ts → Res) :
    thSum (spawnT c i par kid).ths.size (fun j => pSumAt (spawnT c i par kid) j (extZT db c.ths.size j)) =
      thSum c.ths.size (fun j => pSumAt c j (db j)) := by
  unfold thSum; rw [spawnT_size]
  refine rsum_ext (fun j hj => ?_) ?_
  · rw [extZT_lt hj, pSumAt_spawnT_lt hth hpp hj]
  · simp only [extZT_self, pSumAt_spawnT_kid hkp]

/-- The per-key credit sum after the spawn. -/
theorem nsum_cr_spawnT (Tot HP : Nat → Res) (cr : Nat → Ts → Res) (key : Key) :
    ((List.range (spawnT c i par kid).ths.size).map (fun j =>
        (extZ Tot c.ths.size j + extZ HP c.ths.size j + pSumAt (spawnT c i par kid) j (extZT cr c.ths.size j)) key)).sum =
      ((List.range c.ths.size).map (fun j => (Tot j + HP j + pSumAt c j (cr j)) key)).sum := by
  rw [spawnT_size]
  refine nsum_ext (fun j hj => ?_) ?_
  · rw [extZ_lt hj, extZ_lt hj, extZT_lt hj, pSumAt_spawnT_lt hth hpp hj]
  · simp only [extZ_self, extZT_self, pSumAt_spawnT_kid hkp]; rfl

/-- The per-key debit sum after the spawn. -/
theorem nsum_db_spawnT (db : Nat → Ts → Res) (key : Key) :
    ((List.range (spawnT c i par kid).ths.size).map (fun j =>
        pSumAt (spawnT c i par kid) j (extZT db c.ths.size j) key)).sum =
      ((List.range c.ths.size).map (fun j => pSumAt c j (db j) key)).sum := by
  rw [spawnT_size]
  refine nsum_ext (fun j hj => ?_) ?_
  · rw [extZT_lt hj, pSumAt_spawnT_lt hth hpp hj]
  · simp only [extZT_self, pSumAt_spawnT_kid hkp]; rfl

/-- **`bal`** after the spawn. -/
theorem bal_spawnT {Init : Res} {MintOK : Res → Prop} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : ∃ M, MintOK M ∧ thSum c.ths.size (fun j => Tot j + pSumAt c j (cr j) + HP j) + HS ≤
      Init + M + thSum c.ths.size (fun j => pSumAt c j (db j))) :
    ∃ M, MintOK M ∧ thSum (spawnT c i par kid).ths.size (fun j => extZ Tot c.ths.size j +
        pSumAt (spawnT c i par kid) j (extZT cr c.ths.size j) + extZ HP c.ths.size j) + HS ≤
      Init + M + thSum (spawnT c i par kid).ths.size (fun j => pSumAt (spawnT c i par kid) j (extZT db c.ths.size j)) := by
  rw [thSum_bal_spawnT hth hpp hkp, thSum_db_spawnT hth hpp hkp]; exact h

/-- **`knet`** after the spawn. -/
theorem keyNet_spawnT {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {key : Key}
    (h : KeyNet c Tot HP HS cr db key) :
    KeyNet (spawnT c i par kid) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS (extZT cr c.ths.size)
      (extZT db c.ths.size) key := by
  unfold KeyNet at h ⊢
  rw [nsum_cr_spawnT hth hpp hkp, nsum_db_spawnT hth hpp hkp]; exact h

/-- **`rid`** after the spawn. -/
theorem ridOK_spawnT {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {rc : Nat → Nat}
    (h : RidOK c Tot HP HS cr db rc) :
    RidOK (spawnT c i par kid) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS (extZT cr c.ths.size)
      (extZT db c.ths.size) rc := by
  intro n hn key hk
  rw [nsum_cr_spawnT hth hpp hkp, nsum_db_spawnT hth hpp hkp]; exact h n hn key hk

/-- The stride-free core of **`ownF`**: a label no thread's credits name stays unnamed. -/
theorem ownZ_spawnT {Tot HP : Nat → Res} {cr : Nat → Ts → Res} {l : AllocLabel}
    (h : ∀ m, m < c.ths.size → (Tot m + HP m + pSumAt c m (cr m)) (.own l) = 0) :
    ∀ m, m < (spawnT c i par kid).ths.size →
      (extZ Tot c.ths.size m + extZ HP c.ths.size m + pSumAt (spawnT c i par kid) m (extZT cr c.ths.size m)) (.own l) = 0 := by
  intro m hm
  rw [spawnT_size] at hm
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
  · rw [extZ_lt hm, extZ_lt hm, extZT_lt hm, pSumAt_spawnT_lt hth hpp hm]; exact h m hm
  · simp only [extZ_self, extZT_self, pSumAt_spawnT_kid hkp]; rfl

end sums

section pool
variable {Eg : GEnv} {c : Cfg} {i : Nat} {th par kid : TTh}

theorem crPl_extZT (cr pl : Nat → Ts → Res) (n : Nat) :
    TermPool.crPl (extZT cr n) (extZT pl n) = extZT (TermPool.crPl cr pl) n := by
  funext j t
  by_cases h : j = n
  · subst h; simp only [TermPool.crPl, extZT_self, Res.add_zero]
  · simp [TermPool.crPl, extZT, h]

variable (hOL : OwnLive Eg c) (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = [])
  (hkp : kid.promises = [])
include hOL hth hnp hpp hkp

/-- **`PoolTag`** after the spawn (pool extended by zero at the kid). -/
theorem poolTag_spawnT {pl : Nat → Ts → Res} (h : TermPool.PoolTag Eg c pl) :
    TermPool.PoolTag (EgK Eg c) (spawnT c i par kid) (extZT pl c.ths.size) := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  refine ⟨fun j thj t hj hne => ?_, fun j thj S hj l cl hl ho hp hnpub => ?_⟩
  · rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
    · rw [extZT_lt hi] at hne
      have := (h.1 _ th t hth hne).1; rw [hnp] at this; cases this
    · rw [extZT_self] at hne; exact absurd rfl hne
    · have hjl : j < c.ths.size := TermSpawn.lt_of_get hj'
      have e : ∀ S, Cut (EgK Eg c) j S = Cut Eg j S := cut_EgK_ne Eg c hjn
      rw [extZT_lt hjl] at hne ⊢
      simp only [e, spawnT_mem, spawnT_pairs]
      exact h.1 j thj t hj' hne
  · rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
    · refine ⟨[], fun t => Res.zero_le _, fun _ hx => absurd hx (List.not_mem_nil), ?_⟩
      intro o tw _ _ hlo
      obtain ⟨hin, -⟩ := hlo
      have e : (stOf (spawnT c j thj kid).mem (spawnT c j thj kid).pairs thj).promises = [] := hpp
      rw [e] at hin
      cases hin
    · have := hOL.1 l cl _ (cutSto_sub hl) ho; omega
    · have hjl : j < c.ths.size := TermSpawn.lt_of_get hj'
      have e : Cut (EgK Eg c) j S = Cut Eg j S := cut_EgK_ne Eg c hjn S
      rw [e] at hl ⊢
      rw [extZT_lt hjl]
      exact h.2 j thj S hj' l cl hl ho hp hnpub

/-- **`OverCrG`** after the spawn. -/
theorem overCrG_spawnT {cr : Nat → Ts → Res} (h : TermOverCr.OverCrG Eg c cr) :
    TermOverCr.OverCrG (EgK Eg c) (spawnT c i par kid) (extZT cr c.ths.size) := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  intro j thj S hj l cl hl ho hp
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
  · exact TermPool.overCr_noPromP hpp
  · have := hOL.1 l cl _ (cutSto_sub hl) ho; omega
  · have hjl : j < c.ths.size := TermSpawn.lt_of_get hj'
    have e : Cut (EgK Eg c) j S = Cut Eg j S := cut_EgK_ne Eg c hjn S
    rw [e] at hl ⊢
    rw [extZT_lt hjl]
    exact h j thj S hj' l cl hl ho hp

/-- **`pool`** after the spawn. -/
theorem pool_spawnT {Init : Res} {MintOK : Res → Prop} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : ∃ pl : Nat → Ts → Res, TermPool.PoolTag Eg c pl ∧ TermOverCr.OverCrG Eg c (TermPool.crPl cr pl) ∧
      (∃ M, MintOK M ∧ thSum c.ths.size (fun j => Tot j + pSumAt c j (TermPool.crPl cr pl j) + HP j) + HS ≤
        Init + M + thSum c.ths.size (fun j => pSumAt c j (db j))) ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS (TermPool.crPl cr pl) db key) ∧
      (∃ rc, RidOK c Tot HP HS (TermPool.crPl cr pl) db rc)) :
    ∃ pl : Nat → Ts → Res, TermPool.PoolTag (EgK Eg c) (spawnT c i par kid) pl ∧
      TermOverCr.OverCrG (EgK Eg c) (spawnT c i par kid) (TermPool.crPl (extZT cr c.ths.size) pl) ∧
      (∃ M, MintOK M ∧ thSum (spawnT c i par kid).ths.size (fun j => extZ Tot c.ths.size j +
          pSumAt (spawnT c i par kid) j (TermPool.crPl (extZT cr c.ths.size) pl j) + extZ HP c.ths.size j) + HS ≤
        Init + M + thSum (spawnT c i par kid).ths.size (fun j => pSumAt (spawnT c i par kid) j (extZT db c.ths.size j))) ∧
      (∀ key, ExclKey key → KeyNet (spawnT c i par kid) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS
        (TermPool.crPl (extZT cr c.ths.size) pl) (extZT db c.ths.size) key) ∧
      (∃ rc, RidOK (spawnT c i par kid) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS
        (TermPool.crPl (extZT cr c.ths.size) pl) (extZT db c.ths.size) rc) := by
  obtain ⟨pl, hT, hO, hB, hK, ⟨rc, hR⟩⟩ := h
  have hpp' : par.promises = th.promises := by rw [hpp, hnp]
  refine ⟨extZT pl c.ths.size, poolTag_spawnT hOL hth hnp hpp hkp hT, ?_, ?_, ?_, ?_⟩ <;>
    rw [crPl_extZT]
  · exact overCrG_spawnT hOL hth hnp hpp hkp hO
  · exact bal_spawnT hth hpp' hkp hB
  · exact fun key hk => keyNet_spawnT hth hpp' hkp (hK key hk)
  · exact ⟨rc, ridOK_spawnT hth hpp' hkp hR⟩

end pool

section easy
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
  {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th par kid : TTh}
  (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
include hN

/-- The `Eg`-only and memory-only clauses after the spawn (`EgK` changes only `fpOf`, the memory is kept). -/
theorem easy_spawnT :
    GStoClo (EgK Eg c) ∧ GStoMg (EgK Eg c) ∧ SharedTyOK (EgK Eg c) ∧ (∀ l, (EgK Eg c).rini l ≤ (EgK Eg c).ini l) ∧
    TermZwIni.ZwIniG (EgK Eg c) ∧ GBoxNamed (EgK Eg c) ∧ TermBoxZ.BoxPV (EgK Eg c) ∧
    TermBoxZ.BoxFrLe (EgK Eg c) (spawnT c i par kid).mem.size ∧
    TermBoxZ.BoxFrLe (EgK Eg c) ((spawnT c i par kid).mem.size - 1) ∧
    TermBoxZ.PayOwn (EgK Eg c) ∧ TermBoxZ.BoxSto (EgK Eg c) ∧ StoNI (EgK Eg c) ∧
    TermUndefZ.UndefAtG (EgK Eg c) (spawnT c i par kid).mem ∧
    TermUndefLow.UndefLowG (EgK Eg c) (spawnT c i par kid).mem ∧
    MsgWordsG (EgK Eg c) (spawnT c i par kid) ∧
    (k.storeDepRts = true → ∀ l cl, (EgK Eg c).sto l = some cl → LayT cl.ty) ∧
    (∀ l cl, (EgK Eg c).sto l = some cl → TermA4.wrapTop cl.ty = true) :=
  ⟨hN.clo, hN.cmg, hN.shty, hN.rle, hN.zwIni, hN.bnamed, hN.boxPV, hN.boxFrLe, hN.boxFrLt, hN.payOwn,
    hN.boxSto, hN.stoNI, hN.undefAt, hN.undefLow, hN.msgWords, hN.stoLay, hN.stoW⟩

/-- **`ownKeyOwn`** after the spawn. -/
theorem ownKeyOwn_spawnT (hth : c.ths[i]? = some th) :
    OwnKeyOwnG (spawnT c i par kid) (EgK Eg c) (extZ Tot c.ths.size) := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  intro j t l hj hT
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hj'⟩
  · rw [extZ_lt hi] at hT; exact hN.ownKeyOwn j th l hth hT
  · exact absurd (by simp) hT
  · rw [extZ_lt (TermSpawn.lt_of_get hj')] at hT; exact hN.ownKeyOwn j t l hj' hT

/-- **`ownPub`** after the spawn. -/
theorem ownPub_spawnT (hth : c.ths[i]? = some th) :
    OwnPubG (spawnT c i par kid) (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  intro l hp
  obtain ⟨h1, h2⟩ := hN.ownPub l hp
  refine ⟨h1, fun hs => ⟨fun j t hj => ?_, (h2 hs).2⟩⟩
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hj'⟩
  · rw [extZ_lt hi, extZ_lt hi]; exact (h2 hs).1 j th hth
  · simp
  · have hjl := TermSpawn.lt_of_get hj'
    rw [extZ_lt hjl, extZ_lt hjl]; exact (h2 hs).1 j t hj'

/-- **`boxFrOwn`** after the spawn: the box owner is not the kid; the parent's `vWr` only grows. -/
theorem boxFrOwn_spawnT (hOL : OwnLive Eg c) (hth : c.ths[i]? = some th) (hvw : th.vs.vWr ≤ par.vs.vWr) :
    TermBoxZ.BoxFrOwn (EgK Eg c) (spawnT c i par kid) := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  intro l B hB t ht
  have hBo := hOL.2 l B hB
  rcases spawnT_get_cases hi ht with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨-, -, hj'⟩
  · rw [e] at hBo; exact Nat.le_trans (hN.boxFrOwn l B hB th (by rw [e]; exact hth)) hvw
  · omega
  · exact hN.boxFrOwn l B hB t hj'

/-- **`cellOwn`** after the spawn: owners stay below the larger size. -/
theorem cellOwn_spawnT : CellOwnerLiveM (EgK Eg c) (spawnT c i par kid) := by
  intro l cl hcl hm
  obtain ⟨h1, h2⟩ := hN.cellOwn l cl hcl hm
  refine ⟨fun j hj => ?_, h2⟩
  rw [spawnT_size]; exact Nat.lt_succ_of_lt (h1 j hj)

/-- **`granW`** after the spawn. -/
theorem granW_spawnT (hth : c.ths[i]? = some th) :
    k.storeDepRts = true → (spawnT c i par kid).ths.size = 0 ∨
      TermPtrRts.GranuleW (EgK Eg c).sto (spawnT c i par kid).mem (spawnT c i par kid).pairs := fun hk =>
  Or.inr ((hN.granW hk).resolve_left (by have := TermSpawn.lt_of_get hth; omega))

end easy

section rts
variable {Eg : GEnv} {c : Cfg} {i : Nat} {th par kid : TTh} {Tot HP : Nat → Res}

/-- The least plant-edge promise after the spawn: the old one off the parent and the kid. -/
theorem tminG_spawnT_ne {j : Nat} (hji : j ≠ i) (hjn : j ≠ c.ths.size) (a : AllocLabel) :
    TermPtrRts.tminG (EgK Eg c) (spawnT c i par kid) j a = TermPtrRts.tminG Eg c j a := by
  unfold TermPtrRts.tminG; rw [spawnT_get_ne hji hjn]; rfl

theorem tminG_nil {E : GEnv} {c : Cfg} {j : Nat} {t : TTh} (hj : c.ths[j]? = some t) (hp : t.promises = [])
    (a : AllocLabel) : TermPtrRts.tminG E c j a = none := by
  unfold TermPtrRts.tminG; rw [hj]; simp only [TermPtrRts.tminOf, stOf, hp]; rfl

variable (hOL : OwnLive Eg c) (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = [])
  (hkp : kid.promises = [])
include hOL hth hnp hpp hkp

/-- The three cases of a thread index after the spawn, with the facts the rts clauses use. -/
theorem spawnT_idx {j : Nat} {t : TTh} (hj : (spawnT c i par kid).ths[j]? = some t) :
    (j = i ∧ t = par ∧ ∀ a, TermPtrRts.tminG (EgK Eg c) (spawnT c i par kid) j a = none ∧
        TermPtrRts.tminG Eg c j a = none) ∨
      (j = c.ths.size ∧ t = kid) ∨ (j ≠ i ∧ j ≠ c.ths.size ∧ j < c.ths.size ∧ c.ths[j]? = some t) := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | h | ⟨h1, h2, h3⟩
  · exact .inl ⟨rfl, rfl, fun a => ⟨tminG_nil hj hpp a, tminG_nil hth hnp a⟩⟩
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨h1, h2, TermSpawn.lt_of_get h3, h3⟩)

/-- **`ptrGL`** after the spawn, given the parent's and the kid's labels (`LblSto`). -/
theorem ptrGL_spawnT (h : TermPtrRts.PtrRtsGL Eg Tot HP c)
    (hLp : TermPtrRts.ThLbl (EgK Eg c) par) (hLk : TermPtrRts.ThLbl (EgK Eg c) kid) :
    TermPtrRts.PtrRtsGL (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size) (spawnT c i par kid) := by
  obtain ⟨hP, hL, hG, hM⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j t a cl f hj hs ho hf hk u hu
    rcases spawnT_idx hOL hth hnp hpp hkp hj with ⟨-, -, hT⟩ | ⟨rfl, rfl⟩ | ⟨hji, hjn, hjl, hj'⟩
    · rw [(hT a).1] at hu; cases hu
    · have := hOL.1 a cl _ hs ho; omega
    · rw [extZ_lt hjl, extZ_lt hjl] at hk; rw [tminG_spawnT_ne hji hjn] at hu
      exact hP j t a cl f hj' hs ho hf hk u hu
  · intro j t hj
    rcases spawnT_idx hOL hth hnp hpp hkp hj with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ | ⟨-, -, -, hj'⟩
    · exact hLp
    · exact hLk
    · exact hL j t hj'
  · intro j a cl f hs ho hf hk
    have hjl : j < c.ths.size := hOL.1 a cl j hs ho
    by_cases hji : j = i
    · subst hji
      rw [extZ_lt hjl, extZ_lt hjl] at hk
      exact absurd (tminG_nil hth hnp a) (hG j a cl f hs ho hf hk)
    · rw [extZ_lt hjl, extZ_lt hjl] at hk; rw [tminG_spawnT_ne hji (Nat.ne_of_lt hjl)]
      exact hG j a cl f hs ho hf hk
  · intro j t a cl f hj hs ho hf hk u hu
    rcases spawnT_idx hOL hth hnp hpp hkp hj with ⟨-, -, hT⟩ | ⟨rfl, rfl⟩ | ⟨hji, hjn, hjl, hj'⟩
    · rw [(hT a).1] at hu; cases hu
    · have := hOL.1 a cl _ hs ho; omega
    · rw [extZ_lt hjl, extZ_lt hjl] at hk; rw [tminG_spawnT_ne hji hjn] at hu
      exact hM j t a cl f hj' hs ho hf hk u hu

/-- **`boxPlantSep`** after the spawn. -/
theorem boxPlantSep_spawnT (h : TermPtrRts.BoxPlantSep Eg Tot HP c) :
    TermPtrRts.BoxPlantSep (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size) (spawnT c i par kid) := by
  intro l B hB o w hw j t a cl f u hj hs ho hf hk hu hn
  rcases spawnT_idx hOL hth hnp hpp hkp hj with ⟨-, -, hT⟩ | ⟨rfl, rfl⟩ | ⟨hji, hjn, hjl, hj'⟩
  · rw [(hT a).1] at hu; cases hu
  · have := hOL.1 a cl _ hs ho; omega
  · rw [extZ_lt hjl, extZ_lt hjl] at hk; rw [tminG_spawnT_ne hji hjn] at hu
    exact h l B hB o w hw j t a cl f u hj' hs ho hf hk hu hn

/-- **`plantIdx`** after the spawn. -/
theorem plantIdx_spawnT (h : TermPlantAtT.PlantIdxG TermPtrRts.tminG Eg Tot HP c) :
    TermPlantAtT.PlantIdxG TermPtrRts.tminG (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size)
      (spawnT c i par kid) := by
  intro j t l cl hj hs ho hpf hK
  rcases spawnT_idx hOL hth hnp hpp hkp hj with ⟨rfl, -, hT⟩ | ⟨rfl, rfl⟩ | ⟨hji, hjn, hjl, hj'⟩
  · have hjl : j < c.ths.size := TermSpawn.lt_of_get hth
    unfold TermPlantAtT.KeyG at hK; rw [extZ_lt hjl, extZ_lt hjl] at hK
    obtain ⟨u, -, hu, -⟩ := h j th l cl hth hs ho hpf hK
    rw [(hT l).2] at hu; cases hu
  · have := hOL.1 l cl _ hs ho; omega
  · unfold TermPlantAtT.KeyG at hK; rw [extZ_lt hjl, extZ_lt hjl] at hK
    rw [tminG_spawnT_ne hji hjn, EgK_fp_ne Eg c hjn]
    exact h j t l cl hj' hs ho hpf hK

/-- **`boxtop`** after the spawn (the outstanding promises are the old ones). -/
theorem boxTop_spawnT (h : BoxTopG Eg c) : BoxTopG (EgK Eg c) (spawnT c i par kid) := by
  intro l B hB
  have e : ∀ t, t ∈ allProms (spawnT c i par kid) ↔ t ∈ allProms c := fun t =>
    mem_allProms_spawnT hth hnp hpp hkp
  simp only [e, spawnT_mem]
  exact h l B hB

/-- **`predHold`** after the spawn. -/
theorem predHold_spawnT (h : TermPredHold.PredHoldG Eg c) :
    TermPredHold.PredHoldG (EgK Eg c) (spawnT c i par kid) := by
  intro j t S a hj hown hpd hPU
  obtain ⟨cl, hcl, ho⟩ := hown
  rcases spawnT_idx hOL hth hnp hpp hkp hj with ⟨rfl, -, -⟩ | ⟨rfl, rfl⟩ | ⟨hji, hjn, hjl, hj'⟩
  · have hjn : j ≠ c.ths.size := Nat.ne_of_lt (TermSpawn.lt_of_get hth)
    rw [cut_EgK_ne Eg c hjn] at hPU
    obtain ⟨u, -, hu, -⟩ := h j th S a hth ⟨cl, hcl, ho⟩ hpd hPU
    rw [hnp] at hu; cases hu
  · have := hOL.1 _ cl _ hcl ho; omega
  · rw [cut_EgK_ne Eg c hjn] at hPU
    exact h j t S a hj' ⟨cl, hcl, ho⟩ hpd hPU

end rts

#print axioms TermSpawnGlobM.pSumAt_spawnT_lt
#print axioms TermSpawnGlobM.pSumAt_spawnT_kid
#print axioms TermSpawnGlobM.rsum_ext
#print axioms TermSpawnGlobM.nsum_ext
#print axioms TermSpawnGlobM.extZ_lt
#print axioms TermSpawnGlobM.extZT_lt
#print axioms TermSpawnGlobM.thSum_bal_spawnT
#print axioms TermSpawnGlobM.thSum_db_spawnT
#print axioms TermSpawnGlobM.nsum_cr_spawnT
#print axioms TermSpawnGlobM.nsum_db_spawnT
#print axioms TermSpawnGlobM.crPl_extZT
#print axioms TermSpawnGlobM.poolTag_spawnT
#print axioms TermSpawnGlobM.overCrG_spawnT
#print axioms TermSpawnGlobM.tminG_spawnT_ne
#print axioms TermSpawnGlobM.tminG_nil
#print axioms TermSpawnGlobM.spawnT_idx
end TermSpawnGlobM

#print axioms TermSpawnGlobM.bal_spawnT
#print axioms TermSpawnGlobM.keyNet_spawnT
#print axioms TermSpawnGlobM.ridOK_spawnT
#print axioms TermSpawnGlobM.ownZ_spawnT
#print axioms TermSpawnGlobM.pool_spawnT
#print axioms TermSpawnGlobM.easy_spawnT
#print axioms TermSpawnGlobM.ownKeyOwn_spawnT
#print axioms TermSpawnGlobM.ownPub_spawnT
#print axioms TermSpawnGlobM.boxFrOwn_spawnT
#print axioms TermSpawnGlobM.cellOwn_spawnT
#print axioms TermSpawnGlobM.granW_spawnT
#print axioms TermSpawnGlobM.ptrGL_spawnT
#print axioms TermSpawnGlobM.boxPlantSep_spawnT
#print axioms TermSpawnGlobM.plantIdx_spawnT
#print axioms TermSpawnGlobM.boxTop_spawnT
#print axioms TermSpawnGlobM.predHold_spawnT

/-! (hygiene) axiom reports for theorems that had none. -/
#print axioms TermSpawnGlobM.extZ_self
#print axioms TermSpawnGlobM.extZT_self
