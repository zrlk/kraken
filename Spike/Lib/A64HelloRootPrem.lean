/-
**hello.w's root-instance premises, collected** (AArch64). The hTop twins (`A64HelloWcWfS`,
`A64HelloWcWfR`, `A64HelloWcPl`, `A64HelloWcW1`) are generic in the root's
choices; wake fixes them at its root (`PlaceW` layout, `immsW2 Λ0 wakeImms`,
`c0W`, `L0T`, `WakeOPremW.W1W`). `HelloRootPrem L lbl` is the one place
where hello's root discharges them, for the runtime layout `L` and the
start's labels `lbl`:

- the layout's facts: helloProg (`hp`), the code base (`hlo`), the abort
  label (`hΛ`), the labels (`hlab`), the take site (`hsite`);
- the level after the allocation (`W1`; wake's `WakeOPremW.W1W`);
- `hmid`'s premises at the box's level (`h2`: after rodata's allocation `l`
  and the box's `l'`): the arena `ar`, the box's landing side and frame
  condition (`msB`, `F0`), the level `W2`, its fence's extra `X2`, its memory
  side `ms2`, the box's extra ghost facts `G`, the
  level's extra fact at the clone `Wc`, and the named premises `hK2`, `hpub2`,
  `x2_off`, `hXr`, `hokb`, `hg`, `hP` (wake's `wake_h1`/`hmid_boxA`
  premises); the clone's refusal is fixed, `ClH` (wake's `WakeOD.ClW`);
- the callee's (`HelloTi2Hat.hti_H`'s) layout and level facts: the start's
  level parameters `Dt`, `Ctx`, `lsize`, `frM` (generic), the words'
  separation `hs`, the second stack in the pool `hsub`, the second TCB's
  words and the counters off the arena (`hmF`, `hnoF`, `hoffT`, `hoffL`,
  `hoffX`).

- No `wc_main` control `c0`, its placement `hc0`/`hctl`/`hC0` or the allocator's
  placement `halloc` (wake's `c0W`, `placedSE_c0WW`, `allocW_placed_new`) and no
  `hplP`/`hplS`: hello's `wc_main` is entered at level 1, its placement by
  `A64HelloWcPlS`, so these wake-shaped fields had no consumer and were dropped.
- `ClH`, `Fresh2H`, `lbl2H` live in `Spike/Lib/A64HelloClH.lean` (same
  namespace).
- `HelloRootPrem.hmid`: `HelloHatA.hmid_boxAH` at the root's premises, each
  ghost's `HMidPAH` by `HelloH1A.hMidPAH_of`.
-/
import Spike.Lib.A64HelloWcPl
import Spike.Lib.A64HelloWcW1
import Spike.Lib.A64HelloHMid
import Spike.Lib.A64HelloWcInv3
import Spike.Lib.A64HelloClH
import Spike.Lib.A64HelloH1A

namespace Spike.Lib.A64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)
open Spike.Lib.HelloHMid (BoxPureH BoxMH CloneMidH slWsH)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Flow.HelloWc (tH)

/-- **hello's root-instance premises** for the runtime layout `L` and the
start's labels `lbl` (row 5j, discharged by the B8 tier). -/
structure HelloRootPrem (L : RuntimeLayout) (lbl : Lbl) : Type where
  hp : L.prog = SccCode.helloProg
  hlo : L.Λ.code.lo = lo
  hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName
  hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x
  hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
  /-- `.rodata` off the stack pool (wake's `WakeOSide.hro_W`, A1 of any
  `PlaceW` output; `htiWH_place`'s `hro`). -/
  hro : L.Λ.rodata.Disjoint L.Λ.stackPool
  /-- The level after the allocation (wake's `WakeOPremW.W1W`). -/
  W1 : Spike.Lib.FragS isaLSE2
  /-- The allocator's arena (wake's `WakeOD.arW`). -/
  ar : Spike.Lib.Arena
  /-- The arena's geometry: the counter off its cells, the box sizes
  (wake's `WakeOD.hok_W`, from `CtrZ`; `XchgWr.nodeW_wrC_rdX1`'s `har`). -/
  har : ar.OK
  /-- The memory side the box's landing is stated at, per rodata's
  allocation (wake's `wake_h1` parameter `ms0`; hello's box lands in `h1`'s
  segment, so the instance is `h1`'s side at no frames). -/
  msB : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.MemSide isaLSE2
  /-- The box's frame condition (wake's `wake_h1` parameter `F0`). -/
  F0 : MachineData → Prop
  /-- The level after the box (wake's `W1W` at `h1`; hello's third level). -/
  W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isaLSE2
  /-- The fence's extra fact at `h2` (wake's `W1X`'s second conjunct, `X1W`). -/
  X2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isaLSE2
  /-- `h2`'s memory side (wake's `WakeH1Inv.ms1W`). -/
  ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame →
    Spike.Lib.MemSide isaLSE2
  /-- The box's ghost facts beyond `BoxPureH` (wake's `H1G`, as `hmid_boxH`'s
  `G`). -/
  G : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat →
    Spike.Lib.Region → (MachineData → Prop) → (Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop) → UInt64 → Prop
  /-- The level's extra fact at the clone's `svc` (wake's `Ret0.StackM (r1W)`
  in `HMidP.wcl`). -/
  Wc : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.Frag isaLSE2
  /-- `h2`'s kernel at no frames (wake's `ms1W`'s `K`, by `rfl` there). -/
  hK2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 l b n l' b' n' []).K = some Scc.Sem.A64.abi
  /-- `h2`'s publication at no frames (wake's `ms1W`'s `pub`). -/
  hpub2 : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → (ms2 l b n l' b' n' []).pub
  /-- `X2` off the clone's and the take site's pcs (wake's `WakeH1Inv.x1W_off`). -/
  x2_off : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → ∀ s c, Scc.Sem.A64.pcOf s ≠ clonePcH L →
    Scc.Sem.A64.pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
    X2 l b n l' b' n' s c []
  /-- The box call's premises carry from `msB` to `h2`'s side (wake's
  `wake_h1` premise `hokb`, `WakeBoxW.okb_ms1`). -/
  hokb : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    ∀ q : Call, q.OKB (msB l b n) L.lab → q.OKB (ms2 l b n l' b' n' []) L.lab
  /-- `h2`'s arena geometry `msB`'s (wake's `wake_h1` premise `hg`, `arW`'s
  geometry). -/
  hg : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' →
    (ms2 l b n l' b' n' []).heap = (msB l b n).heap ∧ (ms2 l b n l' b' n' []).cells = (msB l b n).cells ∧
      (ms2 l b n l' b' n' []).off = (msB l b n).off ∧ (ms2 l b n l' b' n' []).units = (msB l b n).units
  /-- The start's level's debts (`StartWf.WSH`'s `Dt`; wake's `Dt`). -/
  Dt : State → Prop
  /-- The start's level's contexts (`WSH`'s `Ctx`; wake's `Ctx`). -/
  Ctx : Spike.Lib.FragS isaLSE2
  /-- The start's level's sizes (`WSH`'s `lsize`; wake's `ls0`). -/
  lsize : Spike.Lib.A64Consumer.Lsize
  /-- main's frame per `wc_main` control (`WSH`'s `frM`; at hello's run
  `fun c => HelloRdCf.frH c.env`; generic here). -/
  frM : Spike.Lib.Ctl → TermRun.Frame
  /-- The runtime's words separated at the reserve's counter (wake's
  `StartPlaceLy.wsep_W`). -/
  hs : Spike.Lib.A64.WakePh.WSep L (Spike.Lib.A64.Rt.Reserve.ntA L.lab)
  /-- The second stack in the pool (wake's `StartPlaceLy.hsub1_W`, A13's data
  part). -/
  hsub : (r1Of L.lab).Sub L.Λ.stackPool
  /-- The second TCB's words mapped (wake's `LdFacts`; `hti_H`'s `hmF`). -/
  hmF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) true ⟨a, 8⟩ = true
  /-- The second TCB's words off the owned words (`hti_H`'s `hnoF`). -/
  hnoF : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab), ∀ j w,
    (⟨b, 8⟩, w) ∉ own2bH L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) j
  /-- The second TCB's words off the arena (wake's `StartH0Ti.offW_arW`). -/
  hoffT : ∀ b ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (tH L.lab),
    ¬ (ar.heap ≤ b.toNat ∧ b.toNat < ar.heap + 16 * ar.cells) ∧ (⟨b, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The stack lock off the arena (wake's `offW_arW _ lock_mem`). -/
  hoffL : ¬ (ar.heap ≤ L.lockA.toNat ∧ L.lockA.toNat < ar.heap + 16 * ar.cells) ∧
    (⟨L.lockA, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The stack cursor off the arena (wake's `offW_arW _ next_mem`). -/
  hoffX : ¬ (ar.heap ≤ L.nextA.toNat ∧ L.nextA.toNat < ar.heap + 16 * ar.cells) ∧
    (⟨L.nextA, 8⟩ : Loc) ≠ ar.ctrLoc
  /-- The site's range `r1Of` at the take site inside `W2 ∧ X2` (wake's
  `X1W`'s take clause, `k1W_iff`'s premise). -/
  hXr : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → ∀ s c, W2 l b n l' b' n' s c [] →
    X2 l b n l' b' n' s c [] → s.st.2 = L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL →
    Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = r1Of L.lab
  /-- `h1`'s open premises at every ghost of the box (wake's `H1GA`, by
  `hMidPA_of` to `HMidPA`): `HelloH1A.H1GAH` at `h2`'s level, side and
  placement, `WSH` at `ntA`, `ar`, `Dt`, `ClH`, `Ctx`, `lsize`, `frM`;
  `HelloH1A.hMidPAH_of` makes `HelloHatA.HMidPAH` of it (the callee `ti` by
  `HelloTi2Hat.hti_H`, inside `W ∧ X ∧ NoMsrAt` under `TakeCK site r1Of
  ClH`).

  Satisfiable: the antecedent `BoxPureH ∧ G` is exactly the ghost part of
  `BoxMH` at the box's landing (`hmid`'s pre), so `hP` is consumed only at
  the ghosts of the real run's landing (supplier: `h2`'s landing row,
  `land_I3bH`); with `G := H1GAH …` itself, `hP := fun _ _ _ _ _ _ _ _ _ _ _ h => h`. -/
  hP : ∀ l b n l' b' n', Fresh2H ar lbl l b n l' b' n' → ∀ R F J1 t, BoxPureH L F0 n' R F J1 t →
    G l b n l' b' n' R F J1 t →
    Spike.Lib.HelloH1A.H1GAH L (W2 l b n l' b' n') (X2 l b n l' b' n') (Wc l b n l' b' n') (ms2 l b n l' b' n')
      Spike.Lib.HelloSrc.helloSrc (lbl2H lbl l b l' b') l' b' (slWsH l) (Spike.Lib.A64.Rt.Reserve.ntA L.lab) ar Dt (ClH L)
      Ctx lsize frM R F J1 t

namespace HelloRootPrem

variable {L : RuntimeLayout} {lbl : Lbl} (P : HelloRootPrem L lbl)

/-- **`hmid` at `h2`'s indices** (`HelloHatA.hmid_boxAH` at the root's
premises, `HMidPAH` by `HelloH1A.hMidPAH_of`): from the box's landing with
the second stack unmapped (`KeepUn.U r1Of`) past its store to main's clone
inside `W2 ∧ X2` under the take of the site's range or a refusal at `ClH`,
the box's slice at rodata's words `slWsH l`. -/
theorem hmid {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    (hf : Fresh2H P.ar lbl l b n l' b' n') :
    Spike.Lib.SegWS (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs)
      (Spike.Lib.A64ConsumerA.TakeCKS (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (ClH L))
      Spike.Lib.HelloSrc.helloSrc (lbl2H lbl l b l' b') (P.ms2 l b n l' b' n')
      (fun s c fs => BoxMH L (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
        Spike.Lib.A64.KeepUn.U (r1Of L.lab) s ∧ fs = [])
      (CloneMidH L P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n') l' b' (slWsH l) n') :=
  Spike.Lib.HelloHatA.hmid_boxAH P.hp (P.hK2 _ _ _ _ _ _ hf) (P.hpub2 _ _ _ _ _ _ hf) (fun _ h => ClH.pc h)
    (P.x2_off _ _ _ _ _ _ hf) (P.hXr _ _ _ _ _ _ hf) (Spike.Lib.A64.Rt.fitS_of_sub L P.hsub)
    (P.hokb _ _ _ _ _ _ hf) (P.hg _ _ _ _ _ _ hf)
    fun _ _ _ _ hB hG => Spike.Lib.HelloH1A.hMidPAH_of P.hp P.hlo P.hlab P.hsite P.hΛ (fun _ h => h.2)
      (fun _ h => ClH.pc h) P.hs P.hro P.hsub P.hmF P.hnoF P.hoffT P.hoffL P.hoffX hB
      (P.hP _ _ _ _ _ _ hf _ _ _ _ hB hG)

end HelloRootPrem

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.HelloRootPrem.hmid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HelloRootPrem.hmid
