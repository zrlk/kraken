import WeakCore.TermPtrStab
import WeakCore.TermOwnPub
import WeakCore.TermPromAlloc
import WeakCore.TermGranW

/-!
# TermPtrKey: own-key facts across steps (for)

* `ownKey_noIncrease_thread` / `ownKey_noIncrease_other` / `ownKey_noIncrease_prom`: the own-key
  holding (frame + private + shared) at a non-fresh label does not grow across a thread step (the
  stepper's step inequality, no mint off the fresh labels by `AllocGT`; other threads unchanged) and
  a promise step (`PAcct`, credits and debits own-free; frames unchanged).
* `keyHeld_not_seen` / `keyHeld_not_pub` / `keyHeld_not_newPub`: a step that newly makes an own cell
  of the stepper seen (in particular, publishes it) zeroes the stepper's own-key holdings there
  (`SeenOK`).  So a stepper still holding `own a` did not publish `a`.  The link "`PubAt th a` ⇒ the
  step sees `a`" is a hypothesis (`hPS`) supplied by the consumer.
-/

namespace TermPtrKey
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermBal TermOwnKey TermOwnPub
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(ii) thread step, stepper**: at a label the step does not allocate, the stepper's own-key
holding plus the shared holding does not grow. -/
theorem ownKey_noIncrease_thread (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l)) {l : AllocLabel}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) :
    (Tot' + HP') (.own l) + HS' (.own l) ≤ (Tot i + HP i) (.own l) + HS (.own l) := by
  have hle := step_own_le X Y Z hK l
  have hF0 : F (.own l) = 0 := by
    cases e : F (.own l) with
    | zero => rfl
    | succ n => exact absurd (hb1 X Y (Z.toC _ _ _ _ _) l (by rw [e]; exact Nat.succ_ne_zero n)) hnf
  simp only [Res.add_apply]
  omega

/-- **(ii) thread step, stepper, `upd` form.** -/
theorem ownKey_noIncrease_thread_upd (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l)) {l : AllocLabel}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) :
    (upd Tot i Tot' i + upd HP i HP' i) (.own l) + HS' (.own l) ≤ (Tot i + HP i) (.own l) + HS (.own l) := by
  rw [upd_self, upd_self]
  exact ownKey_noIncrease_thread hb1 X Y Z hK hnf

/-- **(ii) thread step, other threads**: frames and private holdings unchanged. -/
theorem ownKey_noIncrease_other {Tot HP : Nat → Res} {Tot' HP' : Res} {i j : Nat} (hji : j ≠ i)
    (l : AllocLabel) :
    (upd Tot i Tot' j + upd HP i HP' j) (.own l) = (Tot j + HP j) (.own l) := by
  rw [upd_other _ _ hji, upd_other _ _ hji]

/-- **(ii) promise step**: the promiser's private plus shared holding at `own l` does not grow
(`PAcct`; the old credits are own-free by `PromCrK`, the new debits by `hdb`). Frames unchanged. -/
theorem ownKey_noIncrease_prom {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0) (l : AllocLabel) :
    HP' (.own l) + HS' (.own l) ≤ HP j (.own l) + HS (.own l) := by
  obtain ⟨S0, -, -, -, -, -, hK⟩ := X.inv.thr j th X.hth
  have hc0 := (TermOwnFresh.promCrK_own hK l).1
  have hA' := congrFun hA (.own l)
  have hd := hdb l
  simp only [Res.add_apply] at hA' hc0
  omega

/-- **(ii) promise step, `upd` form** (any thread `q`; frames are unchanged). -/
theorem ownKey_noIncrease_prom_upd {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res}
    {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0) (q : Nat) (l : AllocLabel) :
    (Tot q + upd HP j HP' q) (.own l) ≤ (Tot q + HP q) (.own l) + HS (.own l) - HS' (.own l) ∨
      (q ≠ j ∧ (Tot q + upd HP j HP' q) (.own l) = (Tot q + HP q) (.own l)) := by
  by_cases hqj : q = j
  · subst hqj
    left
    have h := ownKey_noIncrease_prom X hA hdb l
    rw [upd_self]
    simp only [Res.add_apply]
    omega
  · right
    exact ⟨hqj, by rw [upd_other _ _ hqj]⟩

/-! ### The shared holding is own-free -/

/-- A memory value of an own-free type holds no own key. -/
theorem valOfR_own_zero {E : TEnv} {T : Ty} {ws : List Word} {R : Res} (hno : Ty.noOwnIn [] T = true)
    (h : ValOfR E T ws R) (l : Nat) : R (.own l) = 0 :=
  TermBlkZ.VRR_own_zero l T [] (CE E.unsee) (fun _ => 0) (shp T) ws R hno
    (fun _ _ _ _ h => (h : False).elim) (fun _ _ _ _ h => (h : False).elim) h.1

/-- A cell (value or buffer) of an own-free type holds no own key. -/
theorem cellOKR_own_zero {E : TEnv} {n nr : Nat} {T : Ty} {vals : List Word} {R : Res}
    (hno : Ty.noOwnIn [] T = true) (h : CellOKR E n nr T vals R) (l : Nat) : R (.own l) = 0 := by
  rcases h with ⟨-, h⟩ | ⟨N, e, us, Rs, hT, -, -, -, hlen, rfl, hj⟩
  · exact valOfR_own_zero hno h l
  · subst hT
    simp only [Ty.noOwnIn] at hno
    cases e0 : Res.sum Rs (.own l) with
    | zero => rfl
    | succ k =>
      exfalso
      obtain ⟨Rj, hm, h1⟩ := sum_ne (k := .own l) (by rw [e0]; exact Nat.succ_ne_zero k)
      obtain ⟨j, hjl, hjv⟩ := List.getElem_of_mem hm
      have hj' := hj j Rj (by omega) (by rw [List.getElem?_eq_getElem hjl, hjv])
      by_cases hz : nWords us = 0 ∧ nr ≤ j
      · rw [hj'.1 hz.2 hz.1] at h1; exact h1 rfl
      · have hor : j < nr ∨ 0 < nWords us := by
          rcases Nat.lt_or_ge j nr with h | h
          · exact .inl h
          · right; rcases Nat.eq_zero_or_pos (nWords us) with h' | h'
            · exact absurd ⟨h', h⟩ hz
            · exact h'
        exact h1 (valOfR_own_zero hno (hj'.2 hor) l)

/-- **`heldS_own_zero`**: the shared holding (cells with a frontier, whose types are own-free by
`MemInv`) carries no own key. -/
theorem heldS_own_zero {g : G} {E : TEnv} {s : St} {H : Res} (hm : MemInv g E s) (h : MemHeldS E s H)
    (l : Nat) : H (.own l) = 0 := by
  obtain ⟨L, Rl, -, -, hQ, rfl, hR⟩ := h
  cases e0 : Res.sum (L.map Rl) (.own l) with
  | zero => rfl
  | succ k =>
    exfalso
    obtain ⟨R, hmem, h1⟩ := sum_ne (k := .own l) (by rw [e0]; exact Nat.succ_ne_zero k)
    obtain ⟨l2, hl2, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨f, hf⟩ := hQ l2 hl2
    obtain ⟨hn, hs⟩ := hR l2 hl2
    cases hc : E.sto l2 with
    | none => rw [hn hc] at h1; exact h1 rfl
    | some c =>
      obtain ⟨vals, -, hok⟩ := hs c hc
      exact h1 (cellOKR_own_zero (MemInv_noOwnT hm hc hf) hok l)

/-- The pre-state shared holding of a thread step is own-free. -/
theorem heldS_own_zero_pre
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (l : Nat) : HS (.own l) = 0 := by
  obtain ⟨S0, -, -, hm, -, hHS, -⟩ := X.inv.thr i th X.hth
  exact heldS_own_zero hm hHS l

/-- The post-state shared holding of a thread step is own-free. -/
theorem heldS_own_zero_post {g : G} {η : TEnv} {s : St} {r : Memory × List Ts × TTh} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' : Ts → Res} {Rf Rs H : Res} {cr db δ : Ts → Res}
    (Z : TOut p g η s r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ) (l : Nat) : HS' (.own l) = 0 :=
  heldS_own_zero Z.2.2.1 Z.2.2.2.2.1 l

/-- **(ii) thread step, stepper, without `HS`** (the gate's form). -/
theorem ownKey_noIncrease_thread_noHS (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l)) {l : AllocLabel}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) :
    (Tot' + HP') (.own l) ≤ (Tot i + HP i) (.own l) := by
  have h := ownKey_noIncrease_thread hb1 X Y Z hK hnf
  have h0 := heldS_own_zero_pre X l
  omega

/-- **(ii) promise step, without `HS`**: the promiser's private holding at `own l` does not grow. -/
theorem ownKey_noIncrease_prom_noHS {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res}
    {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0) (l : AllocLabel) :
    HP' (.own l) ≤ HP j (.own l) := by
  have h := ownKey_noIncrease_prom X hA hdb l
  obtain ⟨S0, -, -, hm, -, hHS, -⟩ := X.inv.thr j th X.hth
  have h0 := heldS_own_zero hm hHS l
  omega

/-- **(i) newly seen own cell**: if the step newly sees an own cell `a` of the stepper (no frontier
before), the stepper's new frame and holdings carry no `own a`. -/
theorem keyHeld_not_seen {c : Cfg} {Eg : GEnv} {i : Nat} {th : TTh} {Tot0 : Res} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {g : G} {E' : TEnv} {Tot' HP' HS' : Res}
    (Y : EnvAt p Eg i th Tot0 S ρ η cx Rf Rs)
    (hm : MemInv g (CE η) (stOf c.mem c.pairs th)) (hSK : SeenOK (CE η) E' Tot' (HP' + HS'))
    {a : AllocLabel} (hown : OwnAt (CE η) a) (hpn : Eg.pfr a = none) (hse : E'.seen a) :
    Tot' (.own a) = 0 ∧ HP' (.own a) + HS' (.own a) = 0 := by
  have hpfrE : (CE η).pfr = Eg.pfr := by rw [Y.1]; rfl
  have hns : ¬ (CE η).seen a := fun hsn => by
    obtain ⟨f, hf, -⟩ := hm.2.2.2.2.1 a hsn
    rw [hpfrE, hpn] at hf; cases hf
  obtain ⟨hT, hH⟩ := hSK a hse hns hown
  simp only [Res.add_apply] at hH
  exact ⟨hT, hH⟩

/-- **(i) contrapositive**: a stepper still holding `own a` (an own cell, no frontier before) did not
newly see `a`. -/
theorem keyHeld_not_seen_contra {c : Cfg} {Eg : GEnv} {i : Nat} {th : TTh} {Tot0 : Res}
    {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {g : G} {E' : TEnv}
    {Tot' HP' HS' : Res}
    (Y : EnvAt p Eg i th Tot0 S ρ η cx Rf Rs)
    (hm : MemInv g (CE η) (stOf c.mem c.pairs th)) (hSK : SeenOK (CE η) E' Tot' (HP' + HS'))
    {a : AllocLabel} (hown : OwnAt (CE η) a) (hpn : Eg.pfr a = none)
    (hheld : 0 < (Tot' + HP') (.own a) + HS' (.own a)) : ¬ E'.seen a := fun hse => by
  have h := keyHeld_not_seen Y hm hSK hown hpn hse
  simp only [Res.add_apply] at hheld
  omega

/-- **(i) `keyHeld_not_pub`**: a stepper still holding `own a` (an own cell, no frontier before) did
not publish `a`, given the consumer's link `hPS` (a publish of `a` makes the step see `a`). -/
theorem keyHeld_not_pub {c : Cfg} {Eg : GEnv} {i : Nat} {th : TTh} {Tot0 : Res}
    {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {g : G} {E' : TEnv}
    {Tot' HP' HS' : Res}
    (Y : EnvAt p Eg i th Tot0 S ρ η cx Rf Rs)
    (hm : MemInv g (CE η) (stOf c.mem c.pairs th)) (hSK : SeenOK (CE η) E' Tot' (HP' + HS'))
    {a : AllocLabel} (hown : OwnAt (CE η) a) (hpn : Eg.pfr a = none)
    (hPS : TermOwnG0Defs.PubAt th a → E'.seen a)
    (hheld : 0 < (Tot' + HP') (.own a) + HS' (.own a)) : ¬ TermOwnG0Defs.PubAt th a := fun hp =>
  keyHeld_not_seen_contra Y hm hSK hown hpn hheld (hPS hp)

/-- **(i) `pubd` form**: a label the step newly marks `pubd` (and in Σ afterwards) carries no own key
in the stepper's new frame and holdings (the new-publish branch of `ownPub_thread`). -/
theorem keyHeld_not_newPub
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hSK : SeenOK (CE η) E' Tot' (HP' + HS')) {a : AllocLabel}
    (hl : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pubd a) (hold : ¬ Eg.pubd a)
    (hs : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto a ≠ none) :
    Tot' (.own a) = 0 ∧ HP' (.own a) + HS' (.own a) = 0 := by
  have hpfrE : (CE η).pfr = Eg.pfr := by rw [Y.1]; rfl
  rw [EgT_pubd] at hl
  rcases hl with hl | ⟨hpn, hpe, hse⟩
  · exact absurd hl hold
  rcases Z.1.2.2.2.2.2.1 a with e | ⟨-, F', -, -, -, hown, -⟩ | ⟨hf, -, e⟩
  · rw [e, hpfrE] at hpe; exact absurd hpn hpe
  · exact keyHeld_not_seen Y hm hSK hown hpn hse
  · rw [EgT_sto_fresh (g := gOf p k arch c i) (n := th.nalloc) (n' := r.2.2.nalloc) hf] at hs
    exact absurd e hs

/-! ### (i), consume route (staged on the footprint output) -/

/-- **Staging (the pending `tstep_footprintP/K` output; never in a final theorem)**: a step at a
`publish` naming `a` consumes `a`'s own key (`MintStep.consume`, `C (.own a) ≥ 1`). -/
def PubConsumeC (th : TTh) (C : Res) : Prop := ∀ a, TermOwnG0Defs.PubAt th a → 1 ≤ C (.own a)

/-- **(i) consume route**: a step publishing a non-fresh `a` leaves no own key of `a` in the
stepper's frame or holdings (TOut's inequality with `C (.own a) ≥ 1`, the net bound ≤ 1 before). -/
theorem keyHeld_not_pub_C (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l)) (hPC : PubConsumeC th C) {a : AllocLabel}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc a) (hp : TermOwnG0Defs.PubAt th a) :
    (Tot' + HP') (.own a) + HS' (.own a) = 0 := by
  have hone := TermOwnNet.ownNet_one X.inv a (lt_of_getq X.hth)
  obtain ⟨S0, -, -, -, -, -, hPK⟩ := X.inv.thr i th X.hth
  have hc0 := (TermOwnFresh.promCrK_own hPK a).1
  have hd0 := (TermOwnFresh.promCrK_own Z.2.2.2.2.2.1 a).2
  have hI := Z.2.2.2.2.2.2.2.1 (.own a)
  have hT := congrFun Y.2.2.2.2.2.2 (.own a)
  have hF0 : F (.own a) = 0 := by
    cases e : F (.own a) with
    | zero => rfl
    | succ n => exact absurd (hb1 X Y (Z.toC _ _ _ _ _) a (by rw [e]; exact Nat.succ_ne_zero n)) hnf
  have hC1 := hPC a hp
  simp only [Res.add_apply] at hI hT hc0 hd0 hone ⊢
  rw [TermBal.pSum_congr_key (fun t => hK t a)] at hI
  omega

/-- **(i) consume route, contrapositive**: a stepper still holding `own a` (non-fresh) did not
publish `a`. -/
theorem keyHeld_not_pub_C_contra (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l)) (hPC : PubConsumeC th C) {a : AllocLabel}
    (hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc a) (hheld : 0 < (Tot' + HP') (.own a)) :
    ¬ TermOwnG0Defs.PubAt th a := fun hp => by
  have h := keyHeld_not_pub_C hb1 X Y Z hK hPC hnf hp
  omega

/-- The promise step's own-key bound in `ptrRtsGL_prom`'s form (`ownKey_noIncrease_prom_noHS`). -/
theorem ownKey_prom_le {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res}
    {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0) (q : Nat) (l : AllocLabel) :
    (Tot q + upd HP j HP' q) (.own l) ≤ (Tot q + HP q) (.own l) := by
  by_cases hq : q = j
  · rw [hq, upd_self]
    have h := ownKey_noIncrease_prom_noHS X hA hdb l
    simp only [Res.add_apply]
    omega
  · rw [upd_other _ _ hq]
    exact Nat.le_refl _

/-- **PtrRtsPost at a promise context**: `PtrRtsGL` across the promise of `PCtx`, from
`SysInvN` (`plt`, `promClos` + `promInCut` ⇒ `NoEdgeUnpl`, `boxSto`, `MemOKP` ⇒ `NonPromLbl`), the
`FgnPromClosG` shape (`hFP`, the clause to come) and `CellOwnerLive` (staging). -/
theorem ptrRtsGL_promX {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res}
    {cr' db' : Ts → Res} {N : AllocLabel → Nat} {n : Nat}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (hG : TermPtrRts.PtrRtsGL Eg Tot HP c)
    (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0)
    (hFP : FgnPromClosG Eg c) (hCO : TermPtrStab.CellOwnerLive Eg c)
    (hMC : TermPtrRts.MemRtsCG (EgP Eg P N j n) Tot (upd HP j HP')
      (promise c j a v w)) :
    TermPtrRts.PtrRtsGL (EgP Eg P N j n) Tot (upd HP j HP') (promise c j a v w) :=
  TermPtrStab.ptrRtsGL_prom X.hth hPL X.inv.plt hG (ownKey_prom_le X hA hdb)
    (TermPtrStab.noEdgeUnpl_of X.inv.promClos X.inv.promInCut) hFP
    (TermPtrStab.nonPromLbl_of X.inv hCO X.hth) X.inv.boxSto hMC

end


section NoFulRun
open TermCert TermGlob TermTyped

theorem alloc_nalloc {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : s.nalloc ≤ r.1.nalloc := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  have := storeUnits_nallocT _ _ _ _ s' hs
  dsimp only at this ⊢
  omega

theorem injM_nalloc {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (h : r ∈ injM g s ty j p) : s.nalloc ≤ r.1.nalloc := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_nalloc hs
      dsimp only at this ⊢
      split
      · exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact Nat.le_refl _

theorem evalOp_nalloc {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : s.nalloc ≤ r.1.nalloc := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact Nat.le_refl _ | (rw [(allocBuf_grows _ _ _ _).2.2]; omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact Nat.le_of_eq (loadUnits_nallocT _ _ _ _ hx).symm
         | exact Nat.le_of_eq (storeUnits_nallocT _ _ _ _ _ hx).symm
         | exact alloc_nalloc hx
         | exact Nat.le_refl _)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact Nat.le_trans (Nat.le_of_eq (TermStepper.projM_nalloc hx).symm) (injM_nalloc hy)
         | exact Nat.le_trans (Nat.le_of_eq (loadUnits_nallocT _ _ _ _ hx).symm)
             (Nat.le_of_eq (storeUnits_nallocT _ _ _ _ _ hy).symm))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact Nat.le_trans (Nat.le_of_eq (loadUnits_nallocT _ _ _ _ hx).symm)
             (Nat.le_of_eq (storeUnits_nallocT _ _ _ _ _ hy).symm)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact Nat.le_of_eq (loadUnits_nallocT _ _ _ _ hx).symm)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; rw [(allocBuf_grows _ _ _ _).2.2]; omega)

theorem tstep_nalloc {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) : th.nalloc ≤ r.2.2.nalloc := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact Nat.le_refl _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       exact Nat.le_of_eq (enter_nallocT he).2.symm)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       exact Nat.le_of_eq (enter_nallocT he).2.symm)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_nalloc hx
         | exact Nat.le_refl _)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact Nat.le_trans (Nat.le_of_eq (TermStepper.projM_nalloc hx).symm) (injM_nalloc hy))



/-- (v3c, (ii)) **The footprint with new pair stores typed**: `tstep_footprintK`
whose environment also starts a two-word unit at every pair store of the result at a label new to
it, and whose second words of two-word units there hold no pointer outside pair stores and promises
(`tstep_footprintK_nc`; staged, with `PtrRtsThreadGL` and `FulCnt`). -/
def FootNC (p : Prog) : Prop :=
  ∀ {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p], ProgT p → g.p = p → 0 < g.n → isDone th = false →
    ScopeD th.σs cx th.term → Typed p cx th.term → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    EnvOK p η → TvOK cx → MemInv g (CE η) (stOf mem pairs th) → g.boxFence = true →
    PAx g mem pairs th → PubWinT (CE η) (stOf mem pairs th) th →
    (∀ l, BufInitOn th l → ¬ g.zf l) → (∀ l, TermOwnG0Defs.PubAt th l → g.pf l) →
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧
        (∀ l, TermOwnG0Defs.PubAt th l → E'.pfr l ≠ none) ∧
        (∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → E'.sto m0.loc.label = some cl →
          (CE η).sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset) ∧
        ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
          E'.sto mv.loc.label = some cl → (CE η).sto mv.loc.label = none → mv.loc.offset = o + 1 →
          TwoAtT cl.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1

/-- A new cell's type is laid out. -/
theorem layT_of_newAtT {n0 : Nat} {mem : Memory} {l : AllocLabel} {T : Ty} (h : NewAtT n0 mem l T) : LayT T := by
  rcases h.1 with ⟨L, hL, -⟩ | ⟨K, e, L, rfl, hL, -⟩
  · exact .inl (by rw [hL]; exact Option.some_ne_none _)
  · exact .inr ⟨K, e, rfl, by rw [hL]; exact Option.some_ne_none _⟩


/-- **The location half of `PromAllocF` along a certified solo run** (cf.
`TermPromAlloc.promAlloc_loc`, there at a `TCtx` step): an outstanding promise of the result of a
taken step of a certified run does not lie at a label the step allocates.  The promise is at a cell
of `E'` (`certified_promLoc` from the result, under the run hypotheses `hscR`/`hwinR`), so at a fresh
cell of the stepper without a frontier (`Foot`), in a one-word slot of it (`SWOne` at its
certificate's fulfilling write); the allocation wrote a message there past the old memory
(`NewAtT`), so `LatestSF` at `E'` puts coherence past the promise, against `certified_promAbove`. -/
theorem promAlloc_locS {p : Prog} {k : Promises.Knobs} {arch : Arch} {j : Nat} {Eu Ea : TEnv} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    {c c' : Cfg} (hs : c' ∈ threadSteps p k arch c j) (hc' : Certified p k arch c' j)
    (hscR : ∀ c0, Solo p k arch j c' c0 → Certified p k arch c0 j → ScopeAt p j c0) (hvIR : TermViewInv.ViewInv c')
    (hwinR : ∀ c0, Solo p k arch j c' c0 → Certified p k arch c0 j → NoHoldPubA p k arch Eu Ea j c0)
    {th : TTh} {E E' : TEnv} {r : Memory × List Ts × TTh}
    (hth : c.ths[j]? = some th) (hm : MemInv (gOf p k arch c j) E (stOf c.mem c.pairs th))
    (hSC : StoClo E) (hbf : c.boxFence = true)
    (e1 : c'.mem = r.1) (e2 : c'.pairs = r.2.1) (e3 : c'.ths[j]? = some r.2.2)
    (hr : r ∈ tstep (gOf p k arch c j) c.mem c.pairs th)
    (hF : Foot (gOf p k arch c j) E E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hE' : ThInvE p E' r.2.2) (hm' : MemInv (gOf p k arch c j) E' (stOf r.1 r.2.1 r.2.2))
    (hA : AnchR Eu Ea E' (stOf r.1 r.2.1 r.2.2)) (hxa : Ea = E' ∨ Ext Ea E') (hTA : TermTyped.TidAt j c' E')
    {t : Ts} {m : Msg} (ht : t ∈ r.2.2.promises) (hmt : r.1[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ¬ FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc m.loc.label := by
  intro hF0
  have hlt0 : ∀ u ∈ th.promises, u < c.mem.size := hm.2.2.1
  have hsub := (TermFul.tstep_fulfil hlt0 (MemInv_nopair hm) hr).1
  have hlt : t < c.mem.size := hlt0 t (hsub.subset ht)
  have hm1 : c'.mem[t]? = some m := by rw [e1]; exact hmt
  have hpa : r.2.2.vs.coh m.loc < t := certified_promAbove hc' e3 ht hm1
  have hg : gOf p k arch c' j = gOf p k arch c j := TermTyped.gOf_thread hs
  have hbo : (gOf p k arch c' j).boxFence = true := by rw [hg]; exact hbf
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [e1, e2]
  have hx0 := TermNoHold.InvAtXF_ofA (p := p) (k := k) (arch := arch) e3 hE' (by rw [hg, hst]; exact hm')
    (StoClo_EFoot hF.1 hSC) hbo (by rw [hst]; exact hA) hxa
  have htp : t ∈ TermFul.promsOf c' j := by rw [TermFul.promsOf_some e3]; exact ht
  have hloc := TermNoHold.certified_promLoc (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hscR hvIR hwinR hx0 hTA hc' htp hm1
  have hb := hF.2 _ hF0
  obtain ⟨j0, -, hj0, hl0⟩ := hF0
  have hsL : ∃ cl, E'.sto m.loc.label = some cl := by
    rcases hloc with ⟨cl, hcl⟩ | ⟨jj, hjj, hlj⟩
    · exact ⟨cl, hcl⟩
    · exfalso
      have hi : j < c.ths.size := TermCert.arr_lt hth
      have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size hs
      have hlb : c'.lbase = c.lbase := (threadSteps_lbase hs).1
      rw [TermStep.threadSteps_n hs, hlb] at hlj
      have e := freshLabel_inj (base := c.lbase) (Cfg.lt_n hi) (Cfg.lt_n hi) (hlj.symm.trans hl0)
      omega
  obtain ⟨cl, hsl⟩ := hsL
  rcases hF.1.2.2.1 m.loc.label with e | ⟨-, T, hT, -, -, hN⟩
  · rw [e, hb.1] at hsl; cases hsl
  have hpfr : E'.pfr m.loc.label = none := by
    rcases hF.1.2.2.2.2.2.1 m.loc.label with e | ⟨-, F, -, -, -, hO, -⟩ | ⟨-, -, e⟩
    · exact e.trans hb.2.2.2
    · obtain ⟨cq, hcq, -⟩ := hO; rw [hb.1] at hcq; cases hcq
    · rw [hT] at e; cases e
  have hX : InvAtX p k arch j E' c'.mem.size r.2.2.vs.vWr c' (Ea := Ea) (Eu := Eu) := by
    obtain ⟨thx, E0, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, -, -, -, hIH0⟩ := hx0
    exact ⟨thx, E0, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  obtain ⟨c1, c2, th1, th2, ρ1, η1, cx1, E2, -, -, -, -, -, -, hx1, hE, hTy, htv, hi, hmi, hscope, hpa1, -, -, -, -, -,
    -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hscR hvIR hwinR hX hTA hc' htp hm1
  obtain ⟨cl1, o1, U, us, j1, hcl1, h1o, hus, hj, ho⟩ :=
    SWOne_holds p _ _ _ _ ρ1 η1 cx1 _ _ hE hTy htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa1 hsw
  rw [hx1.2.2.2.2.1 _ _ hT] at hcl1
  cases hcl1
  have hun : NewU c.mem.size r.1 ⟨m.loc.label, m.loc.offset⟩ := by
    rcases hN.1 with ⟨Lw, hLw, hall⟩ | ⟨K, e, Lw, hTe, hLw, hall⟩
    · exact hall _ (by rw [ho]; exact TermPromAlloc.oneAt_lt_acc h1o hLw hus hj)
    · have h1o' : AtOff (.array (.lit K) e) o1 U := by rw [← hTe]; exact h1o
      exact hall _ (by rw [ho]; exact TermPromAlloc.oneAt_lt_arr h1o' hLw hus hj)
  obtain ⟨tu, mu, htu, hmu, hmul⟩ := hun
  have hnp : tu ∉ r.2.2.promises := fun h5 =>
    Nat.lt_irrefl _ (Nat.lt_of_le_of_lt htu (hlt0 tu (hsub.subset h5)))
  have hown : (⟨T, some E.tid⟩ : Cell).owner = some E'.tid := by rw [hF.1.2.1]
  obtain ⟨vals, hcv, hlat, -⟩ := hm'.2.1 _ _ hT hown
  have hol := TermPromAlloc.oneAt_lt_cellOK hcv h1o hus hj
  obtain ⟨-, -, hlater⟩ := hlat (o1 + j1) _ (List.getElem?_eq_getElem hol)
  have hcoh : tu ≤ r.2.2.vs.coh ⟨m.loc.label, o1 + j1⟩ := Nat.le_of_not_lt fun h5 => by
    rcases hlater tu mu h5 hmu (by rw [hmul, ho]) with h6 | ⟨h6, -⟩
    · exact hnp h6
    · exact h6 hpfr
  have hmloc : m.loc = ⟨m.loc.label, o1 + j1⟩ := by rw [← ho]
  rw [hmloc] at hpa
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans htu hcoh) (Nat.lt_trans hpa hlt))

/-- ((1)) The bridge's `ThLbl`: `ThLbl` reads only `pfr`/`box`, which a cut
(`CE η = Cut Eg j S`) shares with `E_g`. -/
theorem thLbl_pb {Eg : GEnv} {E : TEnv} {th : TTh} (hp : E.pfr = Eg.pfr) (hb : E.box = Eg.box)
    (h : TermPtrRts.ThLbl Eg th) : TermPtrRts.ThLbl { pfr := E.pfr, box := E.box } th := by
  have hc : ∀ env, TermPtrRts.EnvLbl Eg env → TermPtrRts.EnvLbl { pfr := E.pfr, box := E.box } env :=
    fun env he x rt ws hm w hw l hn => by
      change E.pfr l ≠ none ∨ E.box l ≠ none
      rw [hp, hb]; exact he x rt ws hm w hw l hn
  exact ⟨hc _ h.1, fun f hf => hc _ (h.2 f hf)⟩

/-- `ThLbl` at a cut from `LblSto`. -/
theorem thLbl_cut {Eg : GEnv} {c : Cfg} {j : Nat} {th : TTh} {S : AllocLabel → Prop}
    (hL : TermPtrRts.LblSto Eg c) (hth : c.ths[j]? = some th) :
    TermPtrRts.ThLbl { pfr := (Cut Eg j S).pfr, box := (Cut Eg j S).box } th :=
  thLbl_pb rfl rfl (hL j th hth)

/-- The start's fresh labels are outside `E_g` (`SysInvN.fresh`), at `sto = Eg.sto`. -/
theorem fresh_sto_none {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (X : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat} {th : TTh} (hth : c.ths[j]? = some th) :
    ∀ q, th.nalloc ≤ q → Eg.sto (freshLabel c.lbase c.n j q) = none :=
  fun q hq => (X.fresh j th hth q hq).1


end NoFulRun

end TermPtrKey

#print axioms TermPtrKey.ownKey_noIncrease_thread
#print axioms TermPtrKey.ownKey_noIncrease_thread_upd
#print axioms TermPtrKey.ownKey_noIncrease_other
#print axioms TermPtrKey.ownKey_noIncrease_prom
#print axioms TermPtrKey.ownKey_noIncrease_prom_upd
#print axioms TermPtrKey.valOfR_own_zero
#print axioms TermPtrKey.cellOKR_own_zero
#print axioms TermPtrKey.heldS_own_zero
#print axioms TermPtrKey.heldS_own_zero_pre
#print axioms TermPtrKey.heldS_own_zero_post
#print axioms TermPtrKey.ownKey_noIncrease_thread_noHS
#print axioms TermPtrKey.ownKey_noIncrease_prom_noHS
#print axioms TermPtrKey.keyHeld_not_seen
#print axioms TermPtrKey.keyHeld_not_seen_contra
#print axioms TermPtrKey.keyHeld_not_pub
#print axioms TermPtrKey.keyHeld_not_newPub
#print axioms TermPtrKey.keyHeld_not_pub_C
#print axioms TermPtrKey.keyHeld_not_pub_C_contra
#print axioms TermPtrKey.ownKey_prom_le
#print axioms TermPtrKey.ptrRtsGL_promX
#print axioms TermPtrKey.promAlloc_locS
#print axioms TermPtrKey.thLbl_cut
#print axioms TermPtrKey.fresh_sto_none
