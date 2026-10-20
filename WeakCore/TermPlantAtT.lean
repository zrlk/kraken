import WeakCore.TermPlantFul
import WeakCore.TermPlantIdxDefs
import WeakCore.TermPlantAtPos

/-! # TermPlantAtT: `PlantAtT` from the plant-index clause and the no-fulfil step

`TermPlantFul.PlantAtT` (the `ObligationsF` field `plantAtT`, under `storeDepRts`) is assembled
from two named facts:

* `IdxAt`: the plant-index clause `PlantIdxG` at every `TCtx` configuration (to become the
  hk-gated `SysInvN` conjunct `plantIdx`).  At an own frontier cell `l` of `j`: if `j` still
  holds the own key of `l` (`KeyG`), the selected plant edge `t` (`tm`, the `tminOf`) is an outstanding promise
  of `j` with `vWr ≤` its view, below which only own promises / `≤ coh` messages lie at `l`,
  and above which every footprint message at `l` lies.  Footprint messages are never
  message `0` by the run lemma `TermPlantAtPos.promPos_run` (via `PromsOK`).
* `NoFulT`: one certified step of the owner keeps the plant edge outstanding and below `vWr`
  (from the `PtrRtsG` module: `noFul_step`, `noFulPlRun`, `winLe_gen`).

Under the key gate `KeyG` (final: `0 < (Tot j + HP j) (.own l)`); off the gate the case
takes `wB := 0`: the stepper's frame holds no own key, so (C) is vacuous.
-/

namespace TermPlantAtT
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The clause at every `TCtx` configuration. -/
def IdxAt (tm : GEnv → Cfg → Nat → AllocLabel → Option Ts) (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop)
    (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → PlantIdxG tm Eg Tot HP c

/-- **No fulfil of the plant edge** at a certified step of the owner, before the publish. -/
def NoFulT (tm : GEnv → Cfg → Nat → AllocLabel → Option Ts) (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop)
    (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel} {cl : Cell} {t : Ts} {mP : Msg},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → k.storeDepRts = true →
    Eg.sto l = some cl → cl.owner = some i → Eg.pfr l ≠ none → KeyG Tot HP i l →
    tm Eg c i l = some t → c.mem[t]? = some mP → t ∈ th.promises → th.vs.vWr ≤ mP.view →
    t ∈ r.2.2.promises ∧ r.2.2.vs.vWr ≤ mP.view

theorem mem_fpAt_cut {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {a : Address} {t : Ts}
    (h : t ∈ FpAt (Cut Eg i S) a) : t ∈ Eg.fpOf i := by
  unfold FpAt at h
  split at h
  · exact h
  · cases h

theorem sto_of_cut {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (h : (Cut Eg i S).sto l = some cl) : Eg.sto l = some cl := by
  rw [Cut_sto] at h
  unfold cutSto at h
  split at h
  · exact h
  · cases h

/-- Footprint promises are positive, from `PromPos` and `PromsOK`. -/
theorem fp_pos {Eg : GEnv} {c : Cfg} {j : Nat} {th : TTh} {u : Ts} (hP : TermPlantAtPos.PromPos c)
    (hO : PromsOK Eg c) (hj : c.ths[j]? = some th) (hu : u ∈ Eg.fpOf j) : 0 < u := by
  have h1 : u ∈ allProms c := (hO j th hj u).1 (List.mem_append_right _ hu)
  obtain ⟨i, th2, hi, hu2⟩ := TermStepper.mem_allProms.1 h1
  exact hP i th2 hi u hu2

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **The key gate excludes published cells**: a published cell carries no own key in any
thread's frame or holdings (`OwnPubG`). -/
theorem key_not_pubd {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {l : AllocLabel} {cl : Cell} (hI : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[j]? = some th) (hsto : Eg.sto l = some cl) (hkey : KeyG Tot HP j l) : ¬ Eg.pubd l := by
  intro hp
  have hz := ((hI.ownPub l hp).2 (by rw [hsto]; exact Option.some_ne_none _)).1 j th hth
  unfold KeyG at hkey
  omega

/-- **`PlantAtT`** from the plant-index clause and the no-fulfil step. -/
theorem plantAtT_of {tm : GEnv → Cfg → Nat → AllocLabel → Option Ts} (hk : k.storeDepRts = true)
    (h0 : TermPlantAtPos.PromPosR p k arch Sp c0)
    (hI : IdxAt tm p k arch Sp Init MintOK c0) (hN : NoFulT tm p k arch Sp Init MintOK c0) :
    TermPlantFul.PlantAtT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs lab cl X Y hsto hown hpf
  obtain ⟨hCE, htid, -, -, -, -, hRf⟩ := Y
  rw [hCE] at hsto hpf
  have hsto' : Eg.sto lab = some cl := sto_of_cut hsto
  have hown' : cl.owner = some i := by rw [hown, CE_tid, htid]
  have hpf' : Eg.pfr lab ≠ none := by rw [Cut_pfr] at hpf; exact hpf
  have hfp : ∀ t, t ∈ FpAt (CE η) ⟨lab, 0⟩ → t ∈ Eg.fpOf i := by
    intro t ht
    rw [hCE] at ht
    exact mem_fpAt_cut ht
  have hU := hI X i th lab cl X.hth hsto' hown' hpf'
  have hP := TermPlantAtPos.promPos_run X.run h0
  by_cases hp : KeyG Tot HP i lab
  · obtain ⟨t, mP, htm, hmP, htP, hle, hA, hB⟩ := hU hp
    refine ⟨t, hA, fun u m hu hm hl => hB u m (hfp u hu) hm hl, fun _ => ?_⟩
    obtain ⟨h1, h2⟩ := hN X hk hsto' hown' hpf' hp htm hmP htP hle
    exact ⟨mP, hmP, h1, h2⟩
  · refine ⟨0, fun t m _ _ ht => Or.inr (Nat.le_trans ht (Nat.zero_le _)),
      fun t m ht _ _ => fp_pos hP X.inv.proms X.hth (hfp t ht), fun hkey => ?_⟩
    exfalso
    have h2 : (Rf + Rs) (.own lab) = Tot i (.own lab) := by rw [hRf]
    have h3 : (Tot i + HP i) (.own lab) = Tot i (.own lab) + HP i (.own lab) := rfl
    have h4 : (Rf + Rs) (.own lab) = Rf (.own lab) + Rs (.own lab) := rfl
    unfold KeyG at hp
    rw [h3] at hp
    rw [h4] at h2
    omega

end

end TermPlantAtT

#print axioms TermPlantAtT.mem_fpAt_cut
#print axioms TermPlantAtT.sto_of_cut
#print axioms TermPlantAtT.fp_pos
#print axioms TermPlantAtT.key_not_pubd
#print axioms TermPlantAtT.plantAtT_of
