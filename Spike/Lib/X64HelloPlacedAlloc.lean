/-
**The caller's source placed in `scc_rt_alloc`, at any frame** (hello.w, x86-64; the twin of
`Spike/Lib/A64HelloPlacedAlloc.lean`): at every node of an allocator called from a function whose call node is at
offset `fr` (its region `R.callee fr (-160) 8`, the call context `CtxG … fr Jn q`), the caller's source is placed
(`PlacedSE`) as at the call. The allocator's nodes are at the call's control or its hold
(`X64SetupPlaced.allocW_of_ctl`), and a caller slot `k` at least a word above the call node's offset
(`fr + 8 ≤ k`) sits outside the callee's region, kept (`CKept`, `DFrame`), there the call state's.

The instance here is `wc_rodata`'s buffer call (`Hello1.RdCtx` at `-48`, `Hello1.aR`); `wc_main`'s box call is
stated over the same `allocW_placedG` once its call context is. What placing the source needs from the call state
is a premise (`hP`).

- `CtxG`: the allocator's call context at offset `fr`, call-node invariant `Jn` (`RdCtx` unfolds to it).
- `placeVal_slot_keptG`: a caller slot `k ≥ fr + 8` across the call.
- `allocW_placedG`: the generic statement.
- `allocW_placed_rdH`: at `wc_rodata`'s call.

Unlike AArch64 (callee region `R.callee fr (-160) 0`, every slot `k ≥ fr` kept, the nodes' controls through
`PlacedAlloc.allocN_ctl`/`placedSE_congr`), the `call` pushed the return address at the call node's offset, so the
callee's region reaches a word above it (`R.callee fr (-160) 8`) and the kept slots are `k ≥ fr + 8`; the nodes'
controls come from `allocW_of_ctl` (the call's control or its hold, which the placement does not read). No absolute
address appears in this file.
-/
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64PlacedSE
import Spike.Lib.X64Hello1Rodata

namespace Spike.Lib.X64.HelloPh.PlacedAlloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Alloc (Call AllocW N)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)

/-- **The allocator's call context at offset `fr`** in the caller's region `R` at the memory `m`: a caller state
`mC`, `σC` at offsets `⟨fr, []⟩` at the call node (`Jn`), entering the allocator at `q`'s entry, the caller's cells
outside the allocator's region as at the call. -/
def CtxG (ms : MemSide isa) (lab : Label → Int64) (R : Region) (fr : Int) (Jn : AS → Ctl → Prop) (q : Call)
    (m : MachineData) : Prop :=
  ∃ mC σC c, Abs R ⟨fr, []⟩ mC σC ∧ Jn σC c ∧ (N lab ms q .e).J (enter fr σC) c ∧ CKept R fr (-160) 8 mC m

/-- **A caller slot across the allocator's call**: above the callee's region (`R.callee fr (-160) 8`), a cell
`k ≥ fr + 8` of the caller's frame `R` is as at the call (`DFrame`, `CKept`), there `σC`'s (`Abs`). -/
theorem placeVal_slot_keptG {R : Region} {fr : Int} {o : SO} {m1 m' : MachineData} {σC : AS} {s : State}
    (hA : Abs R o m1 σC) (hK : CKept R fr (-160) 8 m1 m') (hD : DFrame (R.callee fr (-160) 8) m' s.st.1)
    (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi) {k : Int} (hk : R.Off k) (hk' : fr + 8 ≤ k) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat := by
  obtain ⟨j, hj, hv⟩ := hA.slot k hk
  have hc : ¬ (R.callee fr (-160) 8).Off (k - fr) := fun ⟨_, _, h3⟩ => by
    simp only [Region.callee] at h3; omega
  have hf := Region.addr_toNat_of hR (k := fr) hlo (by omega)
  have hkn := R.addr_toNat hR hk
  have e := hD (R.addr k) (R.addr_fit hR hk) (.inr (by simp only [Region.callee]; omega))
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, e, hK k hk hc, hj, hv]

section Gen

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {Jn : AS → Ctl → Prop} {q : Call} {fr k : Int}

/-- **The caller's source placed at every node of `scc_rt_alloc`**, called at offset `fr`: given that the call
state's slot `k` places the source at the call's control (`hP`). -/
theorem allocW_placedG (hR : R.OK) (hlo : R.lo ≤ fr) (hfr : fr < 0) (hhi : 0 ≤ R.hi) (hk : R.Off k)
    (hk' : fr + 8 ≤ k)
    (hP : ∀ σC, (∃ mC, Abs R ⟨fr, []⟩ mC σC) → Jn σC q.c0 → ∀ s : State,
      placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat → PlacedSE Λ lbl s q.c0 []) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (R.callee fr (-160) 8)
      (fun m => F m ∧ CallerCells R fr (-160) 8 m ∧ CtxG ms (_root_.Executable.labels exe).label R fr Jn q m) := by
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c hD hc => ?_
  obtain ⟨-, -, mC, σC, c', hA, hJ, hN, hK⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  subst hq0
  have h := hP σC ⟨mC, hA⟩ hJ s (placeVal_slot_keptG hA hK hD hR hlo hfr hhi hk hk')
  rcases hc with rfl | ⟨o, rfl⟩
  · exact h
  · exact h

end Gen

section Inst

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {Jc : AS → Ctl → Prop} {q : Call} {k : Int}

/-- **`wc_rodata`'s buffer call** (call node at `-48`, `Hello1.RdCtx`, `Hello1.aR`): `allocW_placedG` at
`fr = -48`. -/
theorem allocW_placed_rdH (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hk : R.Off k) (hk' : -40 ≤ k)
    (hP : ∀ σC, (∃ mC, Abs R ⟨-48, []⟩ mC σC) →
      (Spike.Lib.X64.Flow.Hello1.rN (_root_.Executable.labels exe).label R Jc .call).J σC q.c0 →
      ∀ s : State, placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σC.slot k).toNat →
        PlacedSE Λ lbl s q.c0 []) :
    AllocW ms q (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc (Spike.Lib.X64.Flow.Hello1.aR R)
      (fun m => F m ∧ CallerCells R (-48) (-160) 8 m ∧
        Spike.Lib.X64.Flow.Hello1.RdCtx ms (_root_.Executable.labels exe).label R Jc q m) :=
  allocW_placedG hR hlo (by decide) hhi hk (by omega) hP

/-- `CtxG` at `wc_rodata`'s call (`fr = -48`, `RdCtx`) is inhabited: at any call-node state (`Abs`, the node's
invariant) whose `%rdx` holds the units of its `%rsi` elements, at the call's own memory, for the call `q` read off
the state's registers and the return address cell. -/
example {lab : Label → Int64} {R : Region} {Jc : AS → Ctl → Prop} {ms : MemSide isa} {mC : MachineData} {σC : AS}
    {c : Ctl} (hA : Abs R ⟨-48, []⟩ mC σC) (hJ : (Spike.Lib.X64.Flow.Hello1.rN lab R Jc .call).J σC c)
    (x : String) (a : CoreTerm.At) (τ : CoreLang.Ty) (e : CoreTerm.Expr) (ta : CoreLang.Ty) (ws : List TermRun.Word)
    (hu : σC.regs.rdx.toBitVec = BitVec.ofNat 64 (ms.units σC.regs.rsi.toBitVec.toNat τ)) :
    ∃ q : Call, CtxG ms lab R (-48) (Spike.Lib.X64.Flow.Hello1.rN lab R Jc .call).J q mC ∧
      Spike.Lib.X64.Flow.Hello1.RdCtx ms lab R Jc q mC := by
  have h : CtxG ms lab R (-48) (Spike.Lib.X64.Flow.Hello1.rN lab R Jc .call).J
      ⟨c, x, a, τ, e, ta, ws, σC.regs.rsi.toBitVec.toNat, σC.regs.rdi.toBitVec, σC.regs.rbp.toBitVec,
        σC.slot (-48)⟩ mC :=
    ⟨mC, σC, c, hA, hJ, ⟨rfl, rfl, by simp [enter], rfl, by simp [Spike.Lib.X64.Alloc.Call.k]; rfl, hu⟩,
      fun _ _ _ => rfl⟩
  exact ⟨_, h, h⟩

end Inst

end Spike.Lib.X64.HelloPh.PlacedAlloc

/-- info: 'Spike.Lib.X64.HelloPh.PlacedAlloc.allocW_placedG' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.PlacedAlloc.allocW_placedG
