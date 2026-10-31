/-
**wake.w on x86-64: main's permit, limit and exit pieces past the clone**
(x86-64): the x64 twin of `Spike/Lib/WakeMainInstD.lean`. It
gives `X64WakeMainClosedWS.main_closed_ws`'s premises `hS`, `hlim` and
`hexit` at the placed instance (`L := RuntimeLayout.ofPlaceWX hp i`, main's
TCB `tp = L.pinA + 0 + 8`). The frame condition is `DFrame R m0` of main's
post-clone region `R` from main's memory `m0` after the clone.

- `locIn_tp16_I`, `locIn_tp8_I`: main's permit word `tp + 16` (`pinA + 24`)
  and limit word `tp + 8` (`pinA + 16`) are shared (in `pinned`). They feed
  `X64WakeMainFlag.hA0_of`/`hAoff_of`, which give the per-word premises
  `hA0` and `hoff` below.
- `unmapped_I`: a word that is off the region and unloadable in `m0` stays
  unloadable under the frame condition (`main_closed_ws`'s `hdm` shape).
- `permit_notIn`, `lim_notIn`: neither word is in a placed label
  (`InLabel`). This is the extra conjunct the A64 `wakeMs.mp` carries for
  stores.
- `hS_I` (`hS`): the park's store of `0` to `tp + 16` (`X64WakeHS.permit_free`,
  `mp_rt`, `X64WakeGOf2.gOf2_ne`).
- `cT_ne_I`: the flag's target `cT` (a word of a placed label) is not the
  limit word.
- `limOk_I` (`hlim`): the limit load's `LimOk` at `tp + 8`, with room up to
  any `Z` at least stack 0's limit (`hZ`; `X64WakeHS.lim_free`,
  `PlaceWX.room_of_le`).
- `hexit_I` (`hexit`): past the wait loop's load, a word the memory side
  reads (a number) that represents `1` is the number `1`. So the source's
  test takes `wlRet` (one `LowerNode.localStep_ifeq`), which returns `0`
  (`SrcSem.mainExit`).

**Deviations from A64.**
- The x64 ghost record and its memory side (the twins of `WakeInst.Gh`,
  `wakeMs` and `WakeInstFields.GhOK`) are not on this branch yet. So the lemmas are stated at `msOf
  L.Λ (μ L) rd (wakeG (GOf2 L m0)
  cT) own lbl lsize`, for any `rd`/`own`, with the record's fields `lbl`,
  `lsize`, `cS`, `cT` passed explicitly.
  - `cT_ne_I` takes `GhOK`'s placed-label conjunct as the premises `hl`,
    `ho` and `hT`.
  - `hexit_I` is stated for any memory side whose reads are numbers
    (`hrd`) and whose placed pairs include `Placed Λ lbl` (`hpl`).
  - If the x64 `wakeMs` strengthens `mp` as A64's does (`¬ InLabel` for
    stores), `hS_I` lifts by `permit_notIn`.
- There is no `htls_I`: the x64 wait loop takes the limit's `LimOk`
  directly (`main_closed_ws`'s `hlim` at `tp + 8` with
  `Z = (R.fp 8).addr 0 - 8 - 16`), so `limOk_I` is that piece.
- `pinned_j` is local here, because the x64 `WakeChildSt` twin is separate.
  It is stated directly at `pinA.toNat + 8 j + k`; `pinA_add` is its local
  helper.
-/
import Spike.Lib.X64WakeHS
import Spike.Lib.LowerNode1
import Spike.Lib.X64WakeMainClosedWS

namespace Spike.Lib.X64WakeMainInstD

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep MemRelP Range lrange)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout mp_rt)
open Spike.Lib.X64.PhRec (m0Of μ pin_ne)
open Spike.Lib.X64Consumer (msOf Placed)
open Spike.Lib.WakeG (wakeG)
open Spike.Lib.X64WakeGOf2 (GOf2 gOf2_ne gOf_of_gOf2 pin_ne2)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (wlIf)
open Spike.Lib.Inv2Core (InLabel)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **A word that is off the region and unloadable in `m0`** stays
unloadable under `DFrame` of the region from `m0`. -/
theorem unmapped_I {R : Region} {m0 : MachineData} {a : BitVec 64} (hA0 : Mem.loadInt m0.dmem a 8 = none)
    (hoff : a.toNat + 8 ≤ 2 ^ 64 ∧
      ((a.toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a.toNat)) :
    ∀ m, DFrame R m0 m → Mem.loadInt m.dmem a 8 = none :=
  fun _ hm => (hm a hoff.1 hoff.2).trans hA0

/-- **`main`'s exit past the wait loop's load**: the word read (a number,
`hrd`) represents `1`, so it is the number `1`. The source's test then takes
`wlRet`, a placed control (`hpl`) whose return is `exit` with code `0`. This
holds for any state predicate `X` (the `At` of `main_closed_ws`'s `hexit`). -/
theorem hexit_I {ms : MemSide isa} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    (hrd : ∀ w', ms.rd w' → ∃ n, w'.val = .num n) (hpl : ∀ s c, Placed Λ lbl s c → ms.pl s c)
    {w : TermRun.Word} {X : State → Ctl → Prop} :
    ∀ s c', Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c' → X s c' →
      ¬ ms.abortAt s → MainExit Spike.Lib.X64WakeT1.wakeSrc ms s c' 0 := by
  rintro s c' ⟨w', ⟨hr, hv⟩, rfl⟩ - -
  have h1 : w'.val = .num 1 := by
    obtain ⟨n, hn⟩ := hrd w' hr
    rw [hn] at hv ⊢
    rw [hv.2]
  have ha : TermRun.evalAt (("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env) (.var "d")
      = some (loadTy (.ptr .pub .int), [w']) := by
    simp [TermRun.evalAt, TermRun.lookupE, List.find?]
  have hs := LowerNode.localStep_ifeq (p := Spike.Lib.X64WakeT1.wakeSrc) (n := 1) (m := 1)
    (c := ⟨wlIf, ("d", loadTy (.ptr .pub .int), [w']) :: (waitC w).env, none⟩)
    (ta := loadTy (.ptr .pub .int)) (tb := .intS (.lit 1)) (wb := TermRun.cst (.num 1))
    rfl ha rfl h1 rfl
  rw [ite_eq_left rfl] at hs
  refine ⟨_, .single hs, hpl s _ ⟨fun _ _ => none, ?_, ?_, ?_⟩, ?_⟩
  · intro x ty ws hl k wd wp hk hp
    cases hp
  · intro x hx
    simp [WakeMLive.wlRet, Scc.Sem.exprFv, Scc.Sem.atVars] at hx
  · intro x k n h
    cases h
  · intro s0 th h0 ht he hst
    unfold Scc.Sem.SrcSem.mainExit
    simp only [h0, ht, hst, he]
    rfl

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- `pinA + c` does not wrap for a small `c`. -/
theorem pinA_add {c : Nat} (hc : c < 2 ^ 32) :
    ((RuntimeLayout.ofPlaceWX hp i).pinA + BitVec.ofNat 64 c).toNat =
      (RuntimeLayout.ofPlaceWX hp i).pinA.toNat + c := by
  have := (RuntimeLayout.ofPlaceWX hp i).words_small _ (RuntimeLayout.ofPlaceWX hp i).pin_mem
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- **The first TCB's word `j` (`0 < j < 7`) has its bytes in `pinned`**:
it is clear of `.data` (A8's `rtOffOk`), so its runtime-word bytes
(`words_mapped`) are in `pinned`. -/
theorem pinned_j {j : Nat} (hj : j < 7) (hj0 : 0 < j) :
    ∀ k < 8, (RuntimeLayout.ofPlaceWX hp i).Λ.pinned.contains
      (((RuntimeLayout.ofPlaceWX hp i).pinA + BitVec.ofNat 64 (8 * j)).toNat + k) := by
  intro k hk
  have hc := Scc.Cert.Rt.X64.clear_of_rtOffOk (PlaceWX.rtOff_of_placeWX hp) (j := j) hj
  change Scc.Cert.Rt.X64.clearB (RuntimeLayout.ofPlaceWX hp i).Λ.data
      ((RuntimeLayout.ofPlaceWX hp i).pinA + BitVec.ofNat 64 (8 * j)) = true ∧ _ at hc
  have hm := (RuntimeLayout.ofPlaceWX hp i).words_mapped _
    ((RuntimeLayout.ofPlaceWX hp i).fld_mem (i := j - 1) (by omega))
  rw [show j - 1 + 1 = j by omega] at hm
  have hb := hm.2.2 k hk
  simp only [Scc.Cert.Rt.X64.clearB, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hb with hb | hb
  · simp only [Range.contains] at hb; omega
  · exact hb

/-- **main's permit word is shared** (`pinned`). -/
theorem locIn_tp16_I :
    Consumer1.LocIn (RuntimeLayout.ofPlaceWX hp i).Λ.shared
      ⟨(RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 16#64, 8⟩ := by
  intro k hk
  rw [X64WakeHS.permit_eq]
  exact .inr (.inr (pinned_j hp i (j := 3) (by decide) (by decide) k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))

/-- **main's limit word is shared** (`pinned`). -/
theorem locIn_tp8_I :
    Consumer1.LocIn (RuntimeLayout.ofPlaceWX hp i).Λ.shared
      ⟨(RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ := by
  intro k hk
  rw [X64WakeHS.lim_eq]
  exact .inr (.inr (pinned_j hp i (j := 2) (by decide) (by decide) k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))

/-- **main's permit word is in no placed label** (`X64WakeHS.permit_free`). -/
theorem permit_notIn {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tq0 tq sp) :
    ¬ InLabel lbl lsize ⟨(RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 16#64, 8⟩ :=
  fun ⟨l, b, hl, hx⟩ => X64WakeHS.permit_free hp i hm ⟨l, b, hl, hx⟩

/-- **main's limit word is in no placed label** (`X64WakeHS.lim_free`). -/
theorem lim_notIn {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tq0 tq sp) :
    ¬ InLabel lbl lsize ⟨(RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ :=
  fun ⟨l, b, hl, hx⟩ => X64WakeHS.lim_free hp i hm ⟨l, b, hl, hx⟩

/-- **`hS` at the instance**: the park's store of `0` to main's permit word
`tp + 16`, under `msOf` at `wakeG (GOf2 L m0) cT`, in main's frame after the
clone. It needs the word unloadable there (`hA0`, `hoff`:
`X64WakeMainFlag.hA0_of`/`hAoff_of` at `locIn_tp16_I`). -/
theorem hS_I {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {rd : TermRun.Word → Prop} {own : Spike.Lib.X64Consumer.Own} {cT : Loc}
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 16#64) 8 = none)
    (hoff : (tp + 16#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 16#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 16#64).toNat)) :
    Spike.Lib.X64.Flow.Ret0.StOk
      (msOf (RuntimeLayout.ofPlaceWX hp i).Λ (μ (RuntimeLayout.ofPlaceWX hp i)) rd
        (wakeG (GOf2 (RuntimeLayout.ofPlaceWX hp i) (m0Of (RuntimeLayout.ofPlaceWX hp i).Λ o.prog o.secs)) cT)
        own lbl lsize)
      (DFrame R m0) (tp + 16#64) 0#64 := by
  have hu := unmapped_I hA0 hoff
  subst htp
  have ha : (RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 16#64 ∈ (RuntimeLayout.ofPlaceWX hp i).rtWords := by
    rw [X64WakeHS.permit_eq]; exact (RuntimeLayout.ofPlaceWX hp i).fld_mem (by decide)
  refine ⟨X64WakeHS.permit_free hp i hm, mp_rt ha true, .inr ?_, hu⟩
  rw [X64WakeHS.permit_eq]
  exact gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _

/-- **The flag's target word is not main's limit word**: `cT` is the word
of `cS` in a placed label (`GhOK`'s conjunct: `hl`, `ho`, `hT`), and
`tp + 8` is in none (`X64WakeHS.lim_free`). -/
theorem cT_ne_I {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {cS : WeakMem.Address} {cT : Loc} {b : Nat} (hl : lbl cS.label = some b) (ho : cS.offset < lsize cS.label)
    (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset)) :
    (⟨(RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT := by
  intro h
  have hx : (lrange lsize cS.label b).contains (b + 8 * cS.offset) := by
    have h1 : @LT.lt Nat _ cS.offset (lsize cS.label) := ho
    simp only [lrange, Range.contains]; omega
  have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
  have hw := (PlaceWX.wf_link_of_placeWX i hp).inSpace
  have hd := (hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceWX hp i).Λ.data ∈ (RuntimeLayout.ofPlaceWX hp i).Λ.regions)).2
  have hh := (hw _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceWX hp i).Λ.heap ∈ (RuntimeLayout.ofPlaceWX hp i).Λ.regions)).2
  have hlt : b + 8 * cS.offset < 2 ^ 64 := by
    simp only [Range.contains] at hs; omega
  refine X64WakeHS.lim_free hp i hm ⟨cS.label, b, hl, ?_⟩
  rw [show (RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 8#64 = cT.addr by rw [← h], hT]
  simp only [Scc.Sem.wordLoc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact hx

/-- **The limit load's `LimOk` at the instance** (`main_closed_ws`'s
`hlim`): main's limit word `tp + 8`, under `msOf` at `wakeG (GOf2 L m0) cT`
(the flag `cT` elsewhere, `hcT`, e.g. `cT_ne_I`), in main's frame after the
clone (`hA0`, `hoff` as in `hS_I`, at `locIn_tp8_I`), with room up to any `Z`
at least stack 0's limit (`hZ`). -/
theorem limOk_I {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tq0 tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceWX hp i).Λ lbl lsize ts tm sm tq0 tq sp)
    {rd : TermRun.Word → Prop} {own : Spike.Lib.X64Consumer.Own} {cT : Loc}
    (hcT : (⟨(RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 8#64, 8⟩ : Loc) ≠ cT)
    {tp : BitVec 64} (htp : tp = (RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64)
    {R : Region} {m0 : MachineData} (hA0 : Mem.loadInt m0.dmem (tp + 8#64) 8 = none)
    (hoff : (tp + 8#64).toNat + 8 ≤ 2 ^ 64 ∧
      (((tp + 8#64).toNat : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ (tp + 8#64).toNat))
    {Z : BitVec 64} (hZ : (RuntimeLayout.ofPlaceWX hp i).stacksA.toNat + 4096 ≤ Z.toNat) :
    Spike.Lib.X64.Flow.Ret0.LimOk
      (msOf (RuntimeLayout.ofPlaceWX hp i).Λ (μ (RuntimeLayout.ofPlaceWX hp i)) rd
        (wakeG (GOf2 (RuntimeLayout.ofPlaceWX hp i) (m0Of (RuntimeLayout.ofPlaceWX hp i).Λ o.prog o.secs)) cT)
        own lbl lsize)
      (DFrame R m0) (tp + 8#64) Z := by
  have hu := unmapped_I hA0 hoff
  subst htp
  have ha : (RuntimeLayout.ofPlaceWX hp i).pinA + 0#64 + 8#64 + 8#64 ∈ (RuntimeLayout.ofPlaceWX hp i).rtWords := by
    rw [X64WakeHS.lim_eq]; exact (RuntimeLayout.ofPlaceWX hp i).fld_mem (by decide)
  refine ⟨X64WakeHS.lim_free hp i hm, mp_rt ha false, hu, fun v hv => ?_⟩
  have hg := Spike.Lib.WakeG.wakeG_off hv hcT
  rw [X64WakeHS.lim_eq, ← Spike.Lib.X64.Rt.limA_tcb0] at hg
  exact PlaceWX.room_of_le hp i hZ v (gOf_of_gOf2 hg)

end Inst

/-- info: 'Spike.Lib.X64WakeMainInstD.unmapped_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unmapped_I

/-- info: 'Spike.Lib.X64WakeMainInstD.hexit_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hexit_I

/-- info: 'Spike.Lib.X64WakeMainInstD.pinned_j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pinned_j

/-- info: 'Spike.Lib.X64WakeMainInstD.locIn_tp16_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locIn_tp16_I

/-- info: 'Spike.Lib.X64WakeMainInstD.locIn_tp8_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locIn_tp8_I

/-- info: 'Spike.Lib.X64WakeMainInstD.hS_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_I

/-- info: 'Spike.Lib.X64WakeMainInstD.cT_ne_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cT_ne_I

/-- info: 'Spike.Lib.X64WakeMainInstD.limOk_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms limOk_I

end Spike.Lib.X64WakeMainInstD
