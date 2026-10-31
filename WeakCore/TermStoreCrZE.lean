import WeakCore.TermSeenHid
import WeakCore.TermViewInvH
import WeakCore.TermUndefInv

/-!
# TermStoreCrZE: the epoch half of the former `ObligationsF` field `storeCrZH` (historical)

**Status.**  That `ObligationsF` field is gone: `StoreCrZ` is now `StoreNI ∧
StoreLeafPayAll` (TermStep), and `toObligationsCX` (TermMain) fills `Obligations.storeCrZH` from
`TermStoreNI.storeNI_of` and `TermPiece.storeLeafPay_of`.  The reduction below targets the old
strong form `StoreCrZ0`; nothing outside this module uses it.

**What is proved.**  The field `storeCrZH` (TermMain) asks, at every thread step from a
reachable configuration (`TCtx`, `EnvAt`), for `StoreCrZ0`: every own outstanding promise `t`
at a unit a plain `pub` store writes either carries nothing (`∀ w R, VRes (CE η) m.loc w R →
R = .zero`) or sits at an epoch-counter word unit and has a numeric predecessor.  This module
reduces the field to its **non-epoch half** `NonEpochFree`:

* at a unit that is no non-ghost protocol word (`¬ WordAt`), `VRes` is zero (`VRes_noWord`);
* at an epoch word unit (`P.epoch = true`): `StoreNI` (`TermStoreNI.storeNI_of`, with `SeenHid`
  from `TermSeenHid.seenHid_of`, wired exactly as in `ObligationsF.toObligations`) says the
  promise does not initialise its unit, so it has a non-`undef` predecessor (`pred_of_not_initAt`,
  E1); that predecessor is numeric (`pred_num`, E2): if it is an own promise, the cell is shared
  (a private cell has `VRes = 0`, `VRes_own`) and `SysInvN.promTy` (`PromTyAOK`) types it; if it is
  not an own promise, `MemOKP` (the first conjunct of the stepper's `MemInv`, `SysInvN.thr`) says
  it is `undef` or `WordOK`, and `wordOK_good` at a non-ghost word gives a number.  No `LatestSF`
  / `PromAbove` / `PubDefP` reasoning is needed: `PromTyAOK` covers the own predecessors directly.
* at a non-epoch word unit: `NonEpochFree`.

`storeCrZ0_of_nonEpochFree` is the per-step form; `storeCrZH_of_nonEpochFree` is the field's
exact type under `NonEpochFree` in field form, so that the field becomes textually
"`NonEpochFree` as a field".

**What remained (earlier).**  `NonEpochFree`: at a non-epoch non-ghost word unit the store
writes, no own outstanding promise carries a region token (`VRes = 0`).  The current proof of
`StoreCrZ` pays the fulfilled promises' debits from the stored value instead, so
`NonEpochFree` is no longer needed by any field.

**Note.**  Everything here is read off the pre-state: `TCtx.inv` (`SysInvN` at `c`:
`thr` for `MemInv` at the stepper's cut, `promTy`, `undefAt`), `TCtx.run`/`TCtx.hth` (for
`EnvVR`), and `EnvAt` (the cut identity `CE η = Cut Eg i S`).  No `MemInv` after a publish is
used (`MemInv` across a publish step needs `PubWin` at the publish).
The three extra premises beyond the field's own are existing fields / initial facts: `ObligationsF.progScope`,
`ObligationsF.runDRF0`, and `TermViewInv.ViewInv c0` (a component of `InitOK`, `hI.1`, exactly
as `toObligations` extracts it).
-/

namespace TermStoreCrZE
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermTyped
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 The residual: the non-epoch half -/

/-- **The non-epoch half of `StoreCrZ0`**: for the same
store, units and own promises as `StoreCrZ0`'s premise, at a unit that is a non-ghost
non-epoch protocol word (`WordAt` with `P.epoch = false`), the promise carries nothing
(`StoreCrZ0`'s first disjunct).  By `WordAt_uniq` this is exactly `StoreCrZ0` restricted to
those units: the second disjunct is false there. -/
def NonEpochFree (η : TEnv) (cx : Cx) (s : St) (th : TTh) : Prop :=
  ∀ x rel a v tok e u, th.term = .let_ x (.store rel a v tok) e →
    ((cx.peek a = .ok (.ptr .pub u) ∧ wordOf (.ptr .pub u) = none) ∨
      (cx.peek a = .ok (.loc .pub u) ∧ wordOf (.loc .pub u) = none)) →
    ∀ rt pw ad μ ru us j, evalAt th.env a = some (rt, [pw]) → addrOf pw = some ad →
      cellOf rt = some (μ, ru) → accs ru = some us → j < nWords us →
    ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = offs ad j →
      ∀ n P, WordAt (CE η) m.loc n P → P.epoch = false →
      ∀ w R, VRes (CE η) m.loc w R → R = .zero

/-! ## §2 Generic facts -/

/-- `NonEpochFree` is nothing stronger than `StoreCrZ0`: at a non-epoch word unit the second
disjunct is impossible (`WordAt_uniq`), so `StoreCrZ0` gives it. -/
theorem nonEpochFree_of_storeCrZ0 {η : TEnv} {cx : Cx} {s : St} {th : TTh} (h : StoreCrZ0 η cx s th) :
    NonEpochFree η cx s th := by
  intro x rel a v tok e u hterm hpk rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc n P hw hep w R hv
  rcases h x rel a v tok e u hterm hpk rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc with
    h1 | ⟨⟨n', P', hw', hep'⟩, -⟩
  · exact h1 w R hv
  · obtain ⟨-, rfl⟩ := WordAt_uniq hw hw'
    rw [hep] at hep'; cases hep'

#print axioms nonEpochFree_of_storeCrZ0

/-- Off protocol words, `VRes` is zero. -/
theorem VRes_noWord {E : TEnv} {a : Address} (h : ∀ n P, ¬ WordAt E a n P) {w : Word} {R : Res}
    (hv : VRes E a w R) : R = .zero := by
  rcases hv with ⟨-, -, ⟨n, P, hw, -, -⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩
  · exact absurd hw (h n P)
  · rfl
  · rfl

/-- (E1) A promise that does not initialise its unit has a non-`undef` predecessor. -/
theorem pred_of_not_initAt {mem : Memory} {a : Address} {t : Ts} (h : ¬ InitAt mem a t) :
    ∃ w, PredAt mem a t w ∧ w.val ≠ .undef := by
  unfold InitAt at h
  obtain ⟨w, hw⟩ := Classical.not_forall.1 h
  by_cases hp : PredAt mem a t w
  · by_cases hne : w.val = .undef
    · exact absurd (fun _ => hne) hw
    · exact ⟨w, hp, hne⟩
  · exact absurd (fun h' => absurd h' hp) hw

#print axioms VRes_noWord
#print axioms pred_of_not_initAt

/-! ## §3 (E2) A non-`undef` predecessor at a visible word unit is numeric -/

/-- (E2) **The predecessor is a number.**  At any timestamp `t` at a non-ghost word unit `a` of a
visible cell of the stepper `i`'s cut, a non-`undef` predecessor is numeric: an own-promise
predecessor is typed by `PromTyAOK` (the cell is shared, being visible and in the cut), any other
message by `MemOKP` (`undef` or `WordOK`, the first conjunct of `MemInv` from `SysInvN.thr`). -/
theorem pred_num {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {η : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hCE : CE η = Cut Eg i S) {a : Address} {t : Ts}
    {n : Nat} {P : Proto} (hw : WordAt (CE η) a n P) (hvis : Vis (CE η) a.label)
    {w : Word} (hp : PredAt c.mem a t w) (hne : w.val ≠ .undef) : ∃ k, w.val = .num k := by
  obtain ⟨cl, hcl, hat, hg⟩ := hw
  have hcl' : cutSto Eg i a.label = some cl := by rw [← Cut_sto, ← hCE]; exact hcl
  have hEg : Eg.sto a.label = some cl := cutSto_sub hcl'
  obtain ⟨t0, m0, hlt, hm0, hl0, rfl, -⟩ := hp
  by_cases h0 : t0 ∈ th.promises
  · -- an own predecessor: the cell is shared (visible, in the cut), so `PromTyAOK` types it
    have hsh : Eg.Shared a.label := by
      obtain ⟨-, hin⟩ := cutSto_some.1 hcl'
      rcases hin with hown | hsh
      · by_cases hns : Eg.Shared a.label
        · exact hns
        · exact absurd ⟨⟨cl, hcl, by rw [hCE]; exact hown⟩, by
            rw [hCE, Cut_pfr]
            exact Option.eq_none_iff_forall_not_mem.2 fun v hv => hns ⟨v, hv⟩⟩ hvis
      · exact hsh
    have hty := X.inv.promTy i th t0 m0 X.hth h0 hm0 cl (by rw [hl0]; exact hEg) (by rw [hl0]; exact hsh)
    obtain ⟨k, hk, -⟩ := wordOK_good hty (by rw [hl0]; exact hat) hg
    exact ⟨k, hk⟩
  · -- not an own promise: `MemOKP` at the stepper's cut
    obtain ⟨S', -, -, hMI, -⟩ := X.inv.thr i th X.hth
    have hsto' : (Cut Eg i S').sto m0.loc.label = some cl := by rw [Cut_sto, hl0]; exact hcl'
    rcases hMI.1.1 t0 m0 cl h0 hm0 hsto' with hund | hty
    · exact absurd hund hne
    · obtain ⟨k, hk, -⟩ := wordOK_good hty (by rw [hl0]; exact hat) hg
      exact ⟨k, hk⟩

#print axioms pred_num

/-! ## §4 `StoreCrZ0` from `NonEpochFree` -/

/-- **`StoreCrZ0` from its non-epoch half**, per step.  Beyond the field's own premises
(`TCtx`, `EnvAt`) and `NonEpochFree`, the three premises are the `ObligationsF` fields
`progScope` (O2) and `runDRF0` (O3) and `TermViewInv.ViewInv c0` (from `InitOK`), exactly what
`ObligationsF.toObligations` feeds `TermStoreNI.storeNI_of` / `TermSeenHid.seenHid_of`.
Per unit: no `WordAt` ⇒ `VRes = 0`; a non-epoch word ⇒ `NonEpochFree`; an epoch word ⇒ private
cell (`VRes = 0`) or `StoreNI` + E1 + E2. -/
theorem storeCrZ0_of_nonEpochFree {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hsc : TermScope.ProgScopeOK p = true) (hdrf : TermScope.RunScopeR p k arch Sp c0)
    (hvi : TermViewInv.ViewInvR p k arch Sp c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hne : NonEpochFree η cx (stOf c.mem c.pairs th) th) :
    StoreCrZ0 η cx (stOf c.mem c.pairs th) th := by
  have hni : StoreNI (CE η) (stOf c.mem c.pairs th) th :=
    TermStoreNI.storeNI_of X
      (TermSeenHid.seenHid_of X (fun Y' => TermScope.scope_of hsc hdrf X Y')
        (TermViewInv.envVR_of_run hvi X.run X.hth)
        ⟨congrArg TEnv.sto Y.1, congrArg TEnv.pfr Y.1, congrArg TEnv.ini Y.1, congrArg TEnv.rini Y.1,
          congrArg TEnv.tid Y.1⟩ (TermUndefInv.undefAt_cut X.inv.undefAt (congrArg TEnv.sto Y.1)))
  intro x rel a v tok e u hterm hpk rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc
  by_cases hW : ∃ n P, WordAt (CE η) m.loc n P
  · obtain ⟨n, P, hw⟩ := hW
    by_cases hep : P.epoch = true
    · -- an epoch word unit
      by_cases hvis : Vis (CE η) m.loc.label
      · refine Or.inr ⟨⟨n, P, hw, hep⟩, ?_⟩
        have hnI : ¬ InitAt c.mem m.loc t := by
          rw [hloc]
          exact hni x rel a v tok e hterm rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc
            (Or.inl ⟨n, P, by rw [← hloc]; exact hw⟩)
        obtain ⟨w, hp, hw0⟩ := pred_of_not_initAt hnI
        exact ⟨w, hp, pred_num X Y.1 hw hvis hp hw0⟩
      · exact Or.inl fun w R hv => (VRes_own (Classical.not_not.1 hvis)).1 hv
    · exact Or.inl (hne x rel a v tok e u hterm hpk rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc n P hw
        (Bool.eq_false_iff.2 hep))
  · exact Or.inl fun w R hv => VRes_noWord (fun n P h => hW ⟨n, P, h⟩) hv

#print axioms storeCrZ0_of_nonEpochFree

/-- **The field `storeCrZH` from `NonEpochFree` as a field**: the field's exact type under one
universally quantified hypothesis of the same shape concluding `NonEpochFree` instead of
`StoreCrZ0` (plus the fields `progScope`, `runDRF0` and `ViewInv c0`, see
`storeCrZ0_of_nonEpochFree`). -/
theorem storeCrZH_of_nonEpochFree {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hsc : TermScope.ProgScopeOK p = true) (hdrf : TermScope.RunScopeR p k arch Sp c0)
    (hvi : TermViewInv.ViewInvR p k arch Sp c0)
    (hNE : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
      {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
      {cx : Cx} {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      NonEpochFree η cx (stOf c.mem c.pairs th) th) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
      {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
      {cx : Cx} {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreCrZ0 η cx (stOf c.mem c.pairs th) th :=
  fun X Y => storeCrZ0_of_nonEpochFree hsc hdrf hvi X Y (hNE X Y)

#print axioms storeCrZH_of_nonEpochFree

end TermStoreCrZE
