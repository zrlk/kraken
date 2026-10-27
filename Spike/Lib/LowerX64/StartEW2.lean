/-
**`scc_rt_start`'s states inside `W2`, for any placed output** (x86-64;
the twin of `Spike/Lib/LowerA64/StartEW2.lean`, `startEW_w2`): the
obligations `StartEW` (`Spike/Lib/Rt/X64StartE.lean`) at `nilW W2`, not
moved by the take's outside move, from `_start` to `call scc_rt_main`, the
return point inside `scc_rt_thread_init` the tail's (`tiOf`): each node's
obligation inside `SFacts` (`startEW_sfacts`) and inside `RtX`
(`startEW_rtX`), the two giving `W2` (`rtX_w2`).

- `swEW_gen`: the switch, `xorl %ebp, %ebp` and the call block inside
  `SFacts`, for any program with the start's tail (`swUW_gen_dt`'s first
  three obligations);
- `TcbW.imp` … `StartEW.imp`: an obligation inside `W` from one inside
  `W1` not moved by `K` and one inside `W2` (`BlkW.imp`, `NodeW.imp`);
- `startEW_sfacts`: `StartEW` inside `SFacts` at a placed output
  (`entryW_ofPlaceOK`, `st0W_gen`, `x0WAt_gen`, `swEW_gen`);
- `startEW_w2`: the two combined;
- `rtWords_offArena`: the runtime's words off the output's arena `arOf`;
- `mainHead_of_placeOKAt`, `mainPosOff_of_placeOKAt`: `scc_rt_main`'s head
  (A11, either tail), so `hmain`;
- `startEW_w2A`: `startEW_w2` at `arOf` with both, and the words off the
  arena's counter by `hctr_of_placeOKAt`: no premise left.
-/
import Spike.Lib.LowerX64.RtStartXOf
import Spike.Lib.LowerX64.StartU
import Spike.Lib.Rt.X64SegsS
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Spike.Lib.Rt.X64MainS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND swR SO)
open Spike.Lib.X64.Flow (XStartW)
open Spike.Lib.X64.Flow.Ret0 (TcbG TN TcbW TakeG TK TakeW TiG TI St0W StackM StackOff pinA stacksA limA tpOf
  startN6 startN7 startN8)
open Spike.Lib.X64.Rt (StartEW StartE1W SwEW EntryW X0WAt TiWAt RuntimeLayout InstOk swFSL)
open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-! ## The switch inside `SFacts` -/

section Sw

open Spike.Lib.X64.Rt.MainU
open Spike.Lib.X64.Flow.Ret0 (startTailIn startMain x1L)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl}

/-- **The switch, `xorl %ebp, %ebp` and the call block after them are
inside `SFacts`** (`SwEW`), for any program with the start's tail (`hin`):
`swUW_gen_dt`'s first three obligations, without `scc_rt_main`'s code, in
the new region of depth `L` at the 8-aligned top `top` (`h8`, `hok`, `hL`,
`hL8`), the stack range in the pool (`hsub`) not wrapping (`hfit`). -/
theorem swEW_gen {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : startTailIn cells = true) {c0 : Ctl} (hC0 : CFacts Λ lbl c0) (hsw : SwPh okPc ph lab)
    {R : Region} {F : MachineData → Prop} {tcb top : BitVec 64} {L : Int}
    (h8 : top.toNat % 8 = 0) (hok : (swR top (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    SwEW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R (fun m => F m ∧ StackM rS m) rS tcb top
      c0 L := by
  have h := hin
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, bSw⟩, bXor⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · rw [hI.labOk]
    exact Spike.Lib.X64.Rt.nodeW_reg_post (p := lab x1L + Int64.ofNat 28) hI (by rfl) bSw rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) hsw.sw.1 hsw.sw.2 hsub
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact Spike.Lib.X64.Rt.nodeW_fi_postO (p := lab x1L + Int64.ofNat 31) hI bXor rfl rfl
        (fun _ _ hJ => hJ.1 ▸ hC0) hsw.xor.1 hsw.xor.2 hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) hsub (fun _ h => h.2)
    · exact Spike.Lib.X64.Rt.nodeW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact Spike.Lib.X64.Rt.blkW_postO hI bMain rfl (Spike.Lib.X64.Rt.startMain_okL hL) hok
        (Int.le_refl _) (Int.le_refl _) h8 (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
        (fun _ _ hJ => hJ.1 ▸ hC0) hsw.main
        (fun _ _ _ k hk r => (noRet_false startMain_noRet k hk r).elim)
        (fun _ _ _ => rfl) hsub hfit (fun _ h => h.2)
    · exact Spike.Lib.X64.Rt.blkW_ofFalse fun _ h => hv h.1.1

end Sw

/-! ## Two obligations in one -/

section Imp

variable {W1 W2 W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F M : MachineData → Prop}

/-- `scc_rt_alloc_tcb`'s obligations inside `W` from two. -/
theorem TcbW.imp {q : TcbG} {i : TN} (h1 : TcbW W1 K exe endPc R F q i)
    (h2 : TcbW W2 (fun _ _ => False) exe endPc R F q i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TcbW W K exe endPc R F q i := by
  cases i <;> dsimp only [TcbW] at h1 h2 ⊢ <;> first | exact BlkW.imp h1 h2 hw | exact NodeW.imp h1 h2 hw

/-- `scc_rt_stack_take`'s obligations inside `W` from two. -/
theorem TakeW.imp {q : TakeG} {i : TK} (h1 : TakeW W1 K exe endPc R F M q i)
    (h2 : TakeW W2 (fun _ _ => False) exe endPc R F M q i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TakeW W K exe endPc R F M q i := by
  cases i <;> dsimp only [TakeW] at h1 h2 ⊢ <;>
    first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw
    | exact fun s c hA => hw s c (h1 s c hA) (h2 s c hA)

/-- `scc_rt_thread_init`'s obligations at the return point `x` inside `W`
from two. -/
theorem TiWAt.imp {q : TiG} {x : Label} {i : TI} (h1 : TiWAt W1 K exe endPc R F M q x i)
    (h2 : TiWAt W2 (fun _ _ => False) exe endPc R F M q x i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TiWAt W K exe endPc R F M q x i := by
  cases i <;> dsimp only [TiWAt] at h1 h2 ⊢ <;>
    first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw
    | exact fun g hg j => TakeW.imp (h1 g hg j) (h2 g hg j) hw

/-- `scc_rt_start`'s first nodes inside `W` from two. -/
theorem XStartW.imp {J : Spike.Lib.X64.AS → Ctl → Prop} (h1 : XStartW W1 K exe endPc R F J)
    (h2 : XStartW W2 (fun _ _ => False) exe endPc R F J) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    XStartW W K exe endPc R F J :=
  ⟨BlkW.imp h1.w0 h2.w0 hw, NodeW.imp h1.w1 h2.w1 hw, BlkW.imp h1.w2 h2.w2 hw, NodeW.imp h1.w3 h2.w3 hw⟩

/-- `scc_rt_start` up to `.x0` inside `W` from two. -/
theorem St0W.imp {n0 : BitVec 64} {c0 : Ctl} (h1 : St0W W1 K exe endPc R F n0 c0)
    (h2 : St0W W2 (fun _ _ => False) exe endPc R F n0 c0) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    St0W W K exe endPc R F n0 c0 :=
  ⟨XStartW.imp h1.start h2.start hw, BlkW.imp h1.blk h2.blk hw,
    fun g hg i => TcbW.imp (h1.tcb g hg i) (h2.tcb g hg i) hw⟩

/-- `scc_rt_start` from `.x0` to the switch inside `W` from two. -/
theorem X0WAt.imp {rS : Range} {n0 k0 : BitVec 64} {c0 : Ctl} {x : Label}
    (h1 : X0WAt W1 K exe endPc R F rS n0 k0 c0 x) (h2 : X0WAt W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0 x)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : X0WAt W K exe endPc R F rS n0 k0 c0 x :=
  ⟨BlkW.imp h1.b0 h2.b0 hw, fun g hg i => TiWAt.imp (h1.ti g hg i) (h2.ti g hg i) hw, BlkW.imp h1.fs h2.fs hw,
    NodeW.imp h1.sys h2.sys hw, BlkW.imp h1.sw h2.sw hw⟩

/-- The switch, `xorl %ebp, %ebp` and the call block inside `W` from two. -/
theorem SwEW.imp {rS : Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (h1 : SwEW W1 K exe endPc R F rS tcb top c0 L) (h2 : SwEW W2 (fun _ _ => False) exe endPc R F rS tcb top c0 L)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : SwEW W K exe endPc R F rS tcb top c0 L :=
  ⟨NodeW.imp h1.sw h2.sw hw, fun v => NodeW.imp (h1.xor v) (h2.xor v) hw,
    fun v => BlkW.imp (h1.blk v) (h2.blk v) hw⟩

/-- `_start`'s nodes inside `W` from two. -/
theorem EntryW.imp {lab : Label → Int64} {c0 : Ctl} (h1 : EntryW W1 K exe endPc R F lab c0)
    (h2 : EntryW W2 (fun _ _ => False) exe endPc R F lab c0) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    EntryW W K exe endPc R F lab c0 :=
  ⟨NodeW.imp h1.xor h2.xor hw, NodeW.imp h1.and h2.and hw, BlkW.imp h1.call h2.call hw⟩

/-- `scc_rt_start` up to `scc_rt_main`'s entry inside `W` from two. -/
theorem StartE1W.imp {rS : Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int} {x : Label}
    (h1 : StartE1W W1 K exe endPc R F rS n0 k0 c0 L x)
    (h2 : StartE1W W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0 L x)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : StartE1W W K exe endPc R F rS n0 k0 c0 L x :=
  ⟨St0W.imp h1.s1 h2.s1 hw, X0WAt.imp h1.s2 h2.s2 hw, SwEW.imp h1.s3 h2.s3 hw⟩

/-- **The start's obligations up to `scc_rt_main`'s entry inside `W`** from
two. -/
theorem StartEW.imp {rS : Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int} {x : Label}
    (h1 : StartEW W1 K exe endPc R F rS n0 k0 c0 L x)
    (h2 : StartEW W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0 L x)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : StartEW W K exe endPc R F rS n0 k0 c0 L x :=
  ⟨EntryW.imp h1.e h2.e hw, fun F' hS hK hF =>
    StartE1W.imp (h1.s F' hS hK hF) (h2.s F' hS (Spike.Lib.X64.KStable.none F') hF) hw⟩

end Imp

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

open Spike.Lib.X64.Rt.PhRecOf in
/-- **`scc_rt_start`'s states are inside `SFacts`** (`StartEW`, from
`_start` to `call scc_rt_main`, the return point inside
`scc_rt_thread_init` the tail's) at the record of an output passing
`placeOK`, in any region holding its frame and its callees' below, with
the source control `c0` (`hC0`), the frame condition giving the runtime's
words unloaded (`hFr`), the first stack `rS` (`hrS`) in the pool (`hsub`)
off the region (`hout`), and the new stack's top 8-aligned with its region
of 8-aligned depth `L` (`h8`, `hok`, `hL`, `hL8`). -/
theorem startEW_sfacts {lbl : Lbl} {rS : Range} {c0 : Ctl} {R : Region} {F : MachineData → Prop}
    {k0 : BitVec 64} {L : Int}
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0) :
    StartEW (fun s c => SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) rS
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl s c) (Spike.Lib.X64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0
      c0 L (Spike.Lib.X64.Rt.tiOf o.place.tail) := by
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hR' := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have hout' := Spike.Lib.X64.Flow.Ret0.Inst.out_callee hR (kc := -8) (lo' := -296) (hi' := 8) (by omega)
    (by decide) (by omega) (by omega) hout
  refine ⟨(Spike.Lib.X64.Rt.entryW_ofPlaceOK h i (Dt := fun _ => False) hR (by omega) hhi hC0),
    fun F' _ _ hF' => ⟨?_, ?_, ?_⟩⟩
  · exact Spike.Lib.X64.Rt.st0W_gen h i (Dt := fun _ => False) hC0 hR' (by show (-296 : Int) ≤ -296; omega)
      (by show (8 : Int) ≤ 8; omega) (fun m hm => hFr m (hF' m hm))
  · exact Spike.Lib.X64.Rt.x0WAt_gen h i (Dt := fun _ => False) hC0 hR' (by show (-296 : Int) ≤ -296; omega)
      (by show (8 : Int) ≤ 8; omega) (fun m hm => hFr m (hF' m hm)) hrS hsub hout'
  · rw [hI.labOk]
    exact swEW_gen hI (Spike.Lib.X64.Rt.rtCodeTi_of_placeOKAt h).tail hC0 (swPh_ofPlaceOK h i) h8 hok hL hL8
      hsub (Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub)

open Spike.Lib.LowerNode (FrOk2 ZBad) in
/-- **`scc_rt_start`'s states are inside `W2`** (`StartEW` at `nilW W2`,
from `_start` to `call scc_rt_main`, not moved by the take's outside move)
at the record of an output passing `placeOK`, at the source start's control
`X64Consumer.c0` (`hC0`, `hf0`, placed at no frame `hpl0`) of a program free
of `ZBad` (`hp`): `startEW_sfacts`'s premises, room for the first stack
(`hk`), the runtime's words off the arena's counter and heap (`hoff`) and
`scc_rt_main` positioned off the write abort (`hmain`). -/
theorem startEW_w2 {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl lbl0 : Lbl} {lsize : Lsize} {rS : Range} {R : Region} {F : MachineData → Prop}
    {k0 : BitVec 64} {L : Int} (hp : ProgNoS ZBad p) (hf0 : FrOk2 X64Consumer.c0 [])
    (hC0 : CFacts (Ly).Λ lbl0 X64Consumer.c0) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hoff : ∀ a ∈ (Ly).rtWords, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hmain : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main"))
    (hpl0 : ∀ s, PlacedS (Ly).Λ lbl s X64Consumer.c0 []) :
    StartEW (Spike.Lib.X64.Rt.nilW (W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly))
        rS (Spike.Lib.X64.PhRec.Tk (Ly)) ar J Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab) lbl lsize))
      (Spike.Lib.X64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 X64Consumer.c0 L
      (Spike.Lib.X64.Rt.tiOf o.place.tail) :=
  StartEW.imp (startEW_sfacts h i hC0 hR hlo hhi hFr hrS hsub hout h8 hok hL hL8)
    (startEW_rtX h i (rS := rS) hR hlo hhi hFr hk hoff hmain hL hok hpl0)
    fun _ _ hS hX => by
      obtain rfl := hX.2.2.2
      exact rtX_w2 hp hf0 hS hX

/-- **The runtime's words are off the arena** `arOf` of the output's
layout: their first bytes lie in `.data` or `pinned` (`words_mapped`), both
disjoint from the heap (A1), which holds the arena (`arOf_sub`). -/
theorem rtWords_offArena : ∀ a ∈ (Ly).rtWords,
    ¬ ((Spike.Lib.X64.Rt.arOf (Ly).Λ).heap ≤ a.toNat ∧
      a.toNat < (Spike.Lib.X64.Rt.arOf (Ly).Λ).heap + 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).cells) := by
  intro a ha
  have hs := Spike.Lib.X64.Rt.arOf_sub h
  have hwf := wf_of_placeOKAt h
  have hD := hwf.disjoint.2.2.2.1
  have hP := hwf.disjoint.2.2.2.2.2.2.2.2.1
  have hb := ((Ly).words_mapped a ha).2.2 0 (by omega)
  change Λ.data.contains (a.toNat + 0) ∨ Λ.pinned.contains (a.toNat + 0) at hb
  change ¬ ((Spike.Lib.X64.Rt.arOf Λ).heap ≤ a.toNat ∧
    a.toNat < (Spike.Lib.X64.Rt.arOf Λ).heap + 16 * (Spike.Lib.X64.Rt.arOf Λ).cells)
  simp only [Range.Sub, Range.Disjoint, Range.contains] at hs hD hP hb
  omega

include h in
/-- **`scc_rt_main`'s head at a placed output** (A11, either tail): the
prologue's first block `xHead` right at its label. -/
theorem mainHead_of_placeOKAt : Scc.Cert.Rt.X64.blockAtB o.prog "scc_rt_main" 0 Spike.Lib.X64.Flow.xHead = true := by
  cases hs : o.place.tail with
  | bare =>
    have hm := (Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)).main
    simp only [Spike.Lib.X64.Rt.mainUIn, Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hm
    exact hm.1.1.1.1.1.1.1.1.2
  | setup =>
    obtain ⟨sw, -, hw⟩ := List.any_eq_true.mp (setupOk_of_placeOKAt h hs)
    have hm := Spike.Lib.X64.Rt.mainSIn_of_okS (Bool.and_eq_true _ _ ▸ hw).1
    simp only [Spike.Lib.X64.Rt.mainSIn, Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hm
    exact hm.1.1.1.1.1.1.1.1.1.1.2

/-- **`hmain`: `scc_rt_main` is a position off the write abort** at a
placed output: the first instruction of its prologue
(`mainHead_of_placeOKAt`). -/
theorem mainPosOff_of_placeOKAt : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main") := by
  have := posOff_of_blockAtB (lab := (Ly).lab) (mainHead_of_placeOKAt h) (by decide) (by decide)
  rwa [Spike.Lib.X64.Flow.ofNat_zero'] at this

open Spike.Lib.LowerNode (FrOk2 ZBad) in
/-- **`scc_rt_start`'s states are inside `W2` at the output's arena**
(`startEW_w2` at `arOf`): the runtime's words off the arena by
`rtWords_offArena` and its counter by `hctr_of_placeOKAt`, and `scc_rt_main`
off the write abort by `mainPosOff_of_placeOKAt`. -/
theorem startEW_w2A {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {J : InvS}
    {Dt : State → Prop} {lbl lbl0 : Lbl} {lsize : Lsize} {rS : Range} {R : Region} {F : MachineData → Prop}
    {k0 : BitVec 64} {L : Int} (hp : ProgNoS ZBad p) (hf0 : FrOk2 X64Consumer.c0 [])
    (hC0 : CFacts (Ly).Λ lbl0 X64Consumer.c0) (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hpl0 : ∀ s, PlacedS (Ly).Λ lbl s X64Consumer.c0 []) :
    StartEW (Spike.Lib.X64.Rt.nilW (W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p rd G (Spike.Lib.X64.PhRec.own (Ly))
        rS (Spike.Lib.X64.PhRec.Tk (Ly)) (Spike.Lib.X64.Rt.arOf (Ly).Λ) J Dt (Spike.Lib.X64.WriteAb.Ab (Ly).lab)
        lbl lsize))
      (Spike.Lib.X64.PhRec.K (Ly) rS) (Ly).exe (Ly).endPc R F rS 0#64 k0 X64Consumer.c0 L
      (Spike.Lib.X64.Rt.tiOf o.place.tail) :=
  startEW_w2 h i (ar := Spike.Lib.X64.Rt.arOf (Ly).Λ) hp hf0 hC0 hR hlo hhi hFr hrS hsub hout h8 hok hL hL8 hk
    (fun a ha => ⟨Spike.Lib.X64.Rt.RuntimeLayout.hctr_of_placeOKAt h i a ha, rtWords_offArena h i a ha⟩)
      (mainPosOff_of_placeOKAt h i) hpl0

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.swEW_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swEW_gen

/-- info: 'Spike.Lib.LowerX64.StartEW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StartEW.imp

/-- info: 'Spike.Lib.LowerX64.startEW_sfacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_sfacts

/-- info: 'Spike.Lib.LowerX64.startEW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_w2

/-- info: 'Spike.Lib.LowerX64.rtWords_offArena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtWords_offArena

/-- info: 'Spike.Lib.LowerX64.mainPosOff_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainPosOff_of_placeOKAt

/-- info: 'Spike.Lib.LowerX64.startEW_w2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_w2A

end Spike.Lib.LowerX64
