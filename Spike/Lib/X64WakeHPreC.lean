/-
**wake.w on x86-64: `PreR.hcm` from the clone's facts** (`hcm_of`) and
`X64WakeHPre.hpre_of` with `hCl` narrowed by it (`hpre_ofC`).

`PreR.hcm` asks, at main's `clone`, `%r12` (`c`'s cell) in the heap region
and `%rbx` (main's `ThreadId` word) at main's TCB word `tcbM L`. At the
clone, `ClonePre` places `c`'s label at `%r12` and `mainTidLbl 2` at `%rbx`
under `R1`'s placement `lbl`, which `I2` makes `upd L0 l b` for a fresh `l`
the arena lands at `b` with `n` bytes (`inv0` never reaches the clone):

- `%r12`: `c` is `l` (`hcl_c`), so `%r12 = b`, in the arena (`AllocLand`,
  `n = lsize l > 0`), in the heap (`har`);
- `%rbx`: `mainTidLbl 2` is not the fresh `l` (`L0` places it, `hme`), so
  `%rbx = tcb0 Λ = pinned.lo + 8`, `tcbM L` as a number
  (`PlaceWX.pinA_toNat_ofPlaceWX`).

- `hcm_of`: the two facts from `ClonePre`, `I2` and the data rows.
- `hpre_ofC`: `hpre_of` with `hCl` lacking its last conjunct.
- `hme_W`, `har_W`: the rows `hme`, `har` at `X64.WakeOD.wakeD` (by
  `L0T`'s definition; `arW` is `Rt.arOf`, its cells inside the heap by
  `heapSize_of_placeWX`).
- `hcl_c_W`: the row `hcl_c` at `wakeD` with `h1`'s invariant `inv1W`
  (`X64.WakeH1Inv.cl_of`).
- `hcl0_W`: the row `hcl0` at `wakeD`'s level `W0W`, from `OPrem.h0`'s
  segment (`X64.WakeWf.noClone_of`, `X0W`'s first clause).

**Premises** (data rows, root/instance tier): `hcl0` (`inv0`'s states are
never at the clone's pc: `H0Stmt`'s third conjunct); `hcl_c` (at
`inv1 l b n`'s states at the clone's pc, `c` is bound to `l`'s locative).
`hcl_c`'s source is the box's landing binding `o` to `l`
(`X64.Flow.WakeWc.box_env`) and the publication `c = publish o`
(`X64WakeBoxDefs.boxPubSy`, to `boxPubCtl`, `c` at `l`), kept to the clone
by `h1`'s invariant (`X64.WakeH1Inv.X1W`'s clone clause). At `wakeD`, `hme`,
`har` are `hme_W`, `har_W`; at `inv1W`, `hcl_c` is `hcl_c_W`; at `W0W`, `hcl0`
is `hcl0_W` (from `OPrem.h0`).

**Unlike AArch64** (forced by the x64 shape): A64's `PreR` has `hme`
(main's id register) but no heap fact for `c`'s cell; x64's `PreR.hcm`
needs both, so `c`'s label is tied to the fresh one (`hcl_c`) and the arena
to the heap (`har`). The TCB word is `pinA + 8` as on A64 (`hme_W`).
-/
import Spike.Lib.X64WakeHPre
import Spike.Lib.X64WakeOD
import Spike.Lib.X64PlaceWRt
import Spike.Lib.Rt.X64ArenaOfPlaceW
import Spike.Lib.X64WakeH1Inv
import Spike.Lib.X64WakeX0

namespace Spike.Lib.X64WakeHPreC

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeW1 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64WakeInst (wakeG')
open Spike.Lib.X64WakeOkW (recW)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakeTcbArea (Q2)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64Consumer (HeldOk2 Lbl Lsize)
open Spike.Lib.X64ConsumerA (I2)
open Spike.Lib.X64.WakePh (tcbM ownGXW)
open Spike.Lib.X64WakeSpawnR (ιR QG HPre)
open Spike.Lib.X64WakeLoadT (tcb0 L0T)
open Spike.Lib.X64.Flow.WakeWc (clonePc)
open Spike.Lib.HeapLand (AllocLand)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`PreR.hcm` at the clone** (see the module doc): `%r12` in the heap,
`%rbx` main's TCB word. -/
theorem hcm_of {D : X64WakeO.OData}
    /- `inv0` never reaches the clone -/
    (hcl0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    /- at `inv1 l b n`'s clone states `c` is `l` -/
    (hcl_c : ∀ l b n s (c : Ctl) fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    /- `L0` places main's `ThreadId` label at `tcb0` -/
    (hme : D.L0 (mainTidLbl 2) = some (tcb0 (Ly).Λ))
    /- the arena's cells are in the heap region -/
    (har : (Ly).Λ.heap.lo ≤ D.ar.heap ∧ D.ar.heap + 16 * D.ar.cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size)
    {X : State → Prop} {lbl : Lbl} {lsize : Lsize} {d : Cfg} {s : TermRun.Cfg} {th : Thread isa}
    {th0 : TermRun.TTh} {hd : Option (Nat × TermRun.Word)}
    (hI : I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack)
    (hcl : ClonePre (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s) (hth : d.1.threads = #[th]) (hs : s.ths = #[th0])
    (hX : ∀ st, X st → st.exe = (Ly).exe)
    (hin : ∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
      0 < lsize l) :
    (Ly).Λ.heap.contains (th.st.st.1.regs.get64 .r12).toNat ∧
      BitVec.ofNat 64 (th.st.st.1.regs.get64 .rbx).toNat = tcbM (Ly) := by
  obtain ⟨thc, th0c, tlsc, cA, meW, l, hthc, hsc, hpc, -, -, -, -, -, hr12, hrbx, -, -, -, -, hXs, -, -, -, -,
    -, hc, -, -, hvc, hvm⟩ := hcl
  obtain rfl : thc = th := by
    rw [hth] at hthc; exact (List.singleton_inj.mp (congrArg Array.toList hthc)).symm
  obtain rfl : th0c = th0 := by
    rw [hs] at hsc; exact (List.singleton_inj.mp (congrArg Array.toList hsc)).symm
  have hpc' : pcOf thc.st = clonePc (Ly) := by
    simp only [pcOf, clonePc, hpc, hX _ hXs]
  rcases hI with ⟨-, -, hi⟩ | ⟨l', b, n, hl', hb, rfl, rfl, hi⟩
  · exact absurd hpc' (hcl0 _ _ _ hi)
  have hc' := hcl_c _ _ _ _ _ _ hi hpc'
  have hll : l = l' := by
    have := hc.symm.trans hc'
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at this
    cases this; rfl
  subst hll
  have hn := hin l hc
  simp only [Spike.Lib.X64ConsumerA.updN, ite_true] at hn
  obtain ⟨-, x, hx, hxe⟩ := hvc
  simp only [wordAddr, Spike.Lib.X64ConsumerA.upd, ite_true, Option.map_some, Option.some.injEq] at hx
  obtain ⟨-, y, hy, hye⟩ := hvm
  have hne : mainTidLbl 2 ≠ l := fun h => by rw [← h, hme] at hl'; cases hl'
  simp only [wordAddr, Spike.Lib.X64ConsumerA.upd, hne, ite_false, hme, Option.map_some, Option.some.injEq] at hy
  obtain ⟨hb1, hb2, -⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [hr12, hxe, ← hx]; simp only [Range.contains]; omega
  · rw [hrbx, hye, ← hy]
    have h0 := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hp i
    apply BitVec.eq_of_toNat_eq
    simp only [tcb0, BitVec.toNat_ofNat, BitVec.toNat_add, tcbM, h0]

/-- **`HPre` from `R1O`, `hCl` without `PreR.hcm`** (`hcm_of`; see the
module doc). -/
theorem hpre_ofC {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {D : X64WakeO.OData} {μ' : Marks}
    (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ μ' D d s)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hr0 : ∀ w, r0 w = D.r0) (hr1 : ∀ w, r1 w = r1Of (Ly).lab)
    (hown : ∃ a, ∀ st stk, D.own st stk = ownGXW (Ly) a st)
    (hG : ∀ d s (th : Thread isa) (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) ts hd l T S pT cw,
      R1 d s → d.1.threads = #[th] → s.ths = #[th0] →
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
      Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem → ∀ X, ClonePre (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s →
      MemInv D.G d.1.mem → MemInv (wakeG' hp i (recW T S lbl lsize l pT cw)) d.1.mem)
    /- the clone's facts at `PreJAH`'s witnesses, without `PreR.hcm` -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 (Ly).Λ D.r0 D.r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ (X : State → Prop) (q : TcbGG), ClonePre (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s ∧
        (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = X64WakeAssemblyR.endR hp i ∧ st.decls = {}) ∧
        (∀ st, X st → st.st.2 = cloneAt (Ly).exe ∧ st.st.1.regs.get64 .r8 = tcbOf (Ly).lab q) ∧
        Q2 q ∧ th0.stack = [] ∧
        (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
          0 < lsize l))
    (hcl0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl_c : ∀ l b n s (c : Ctl) fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hme : D.L0 (mainTidLbl 2) = some (tcb0 (Ly).Λ))
    (har : (Ly).Λ.heap.lo ≤ D.ar.heap ∧ D.ar.heap + 16 * D.ar.cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size) :
    HPre hp i asm E arch R1 μ M r0 r1 := by
  refine X64WakeHPre.hpre_of hp i hR1 hpin2 hr0 hr1 hown hG ?_
  intro d s th stack tls r th0 lbl lsize ts hd hP hth hs hσ hp0 hJ hH hInv1
  obtain ⟨X, q, hcl, hX, hXq, hq, hstk, hin⟩ := hCl d s th stack tls r th0 lbl lsize ts hd hP hth hs hσ hp0 hJ hH hInv1
  exact ⟨X, q, hcl, hX, hXq, hq, hstk, hin,
    hcm_of hp i hcl0 hcl_c hme har hJ hcl hth hs (fun st h => (hX st h).1) hin⟩

/-- **`hme` at `wakeD`**: `L0T` places main's `ThreadId` label at `tcb0`. -/
theorem hme_W {E : Scc.Sem.Entry} {cT : Loc} {Dt : State → Prop} {ls0 : Lsize} {W0 inv0 : FragS isa}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} :
    (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).L0 (mainTidLbl 2) = some (tcb0 (Ly).Λ) := by
  simp [Spike.Lib.X64.WakeOD.wakeD, L0T, Spike.Lib.X64ConsumerA.upd]

/-- **`har` at `wakeD`**: `arW`'s cells (`Rt.arOf`: the heap's base,
`allocCells` cells) are in the heap region (`heapSize_of_placeWX`). -/
theorem har_W {E : Scc.Sem.Entry} {cT : Loc} {Dt : State → Prop} {ls0 : Lsize} {W0 inv0 : FragS isa}
    {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} :
    (Ly).Λ.heap.lo ≤ (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.heap ∧
      (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.heap +
        16 * (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.cells ≤
        (Ly).Λ.heap.lo + (Ly).Λ.heap.size := by
  have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hp)
  have hh : (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.heap = (Ly).Λ.heap.lo := rfl
  have hc : (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1).ar.cells = Scc.Cert.PlaceOK.allocCells := rfl
  rw [hh, hc]; omega

/-- **`hcl_c` at `wakeD` with `h1`'s invariant `inv1W`**: `c` is the box
(`X64.WakeH1Inv.cl_of`, `X1W`'s clone clause). -/
theorem hcl_c_W {asm : Asm} {E : Scc.Sem.Entry} {cT : Loc} {Dt : State → Prop} {Ctx : FragS isa}
    {ls0 : Lsize} {W0 inv0 : FragS isa} :
    ∀ l b n s (c : Ctl) fs, (Spike.Lib.X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0
        (Spike.Lib.X64.WakeOPremW.W1W asm hp i E Dt Ctx ls0)
        (Spike.Lib.X64.WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0)).inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :=
  fun l b n => Spike.Lib.X64.WakeH1Inv.cl_of asm hp i E cT Dt Ctx ls0 l b n

/-- **`hcl0` at `wakeD` with the level `W0W`**: an invariant inside `W0W`
(`OPrem.h0`'s segment) is off the clone's pc (`X0W`'s first clause,
`X64.WakeWf.noClone_of`). -/
theorem hcl0_W {asm : Asm} {E : Scc.Sem.Entry} {Dt : State → Prop} {Ctx : FragS isa} {ls0 : Lsize}
    {frM : TermRun.Frame} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isa}
    {inv0 : FragS isa}
    (h0 : Spike.Lib.X64ConsumerA.SegInvS (Spike.Lib.X64.WakeOPremW.W0W asm hp i E Dt Ctx ls0 frM) K wakeSrc
      (L0T (Ly).Λ) ms0 inv0) :
    ∀ s c fs, inv0 s c fs → pcOf s ≠ clonePc (Ly) :=
  Spike.Lib.X64.WakeWf.noClone_of h0

end Inst

/-- info: 'Spike.Lib.X64WakeHPreC.hcm_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcm_of

/-- info: 'Spike.Lib.X64WakeHPreC.hpre_ofC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpre_ofC

/-- info: 'Spike.Lib.X64WakeHPreC.hme_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hme_W

/-- info: 'Spike.Lib.X64WakeHPreC.har_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms har_W

/-- info: 'Spike.Lib.X64WakeHPreC.hcl_c_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcl_c_W

/-- info: 'Spike.Lib.X64WakeHPreC.hcl0_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcl0_W

end Spike.Lib.X64WakeHPreC
