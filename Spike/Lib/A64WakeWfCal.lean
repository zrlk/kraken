/-
**wake.w's `wc_main` callees inside `Wf`** (AArch64): the nodes of
`scc_rt_thread_reserve` (`ReserveW`) and of `scc_rt_alloc_tcb` (`TcbWG`)
as called from `wc_main` (returning to `.sp3`, `.sp4`) inside `WakeWf.Wf` at any frames `fs`, owned words `own`, write tail `Dt` and move
`K`, from the nodes' `SFactsSt2` at `ownG` and `Dt = False` (`hst`) and
placement (`hpl`), both given per node, the nodes' pcs off the sites
(decided against the resolved sites `WakePh.okC`), the abort phases'
decided checks (`phOffW`, `siOffW`), the callee's control (`hc0`) and the
written words off the arena (`hoff*`). The `ret`-free blocks and silent
instructions go through `WcWf.blkW_wfC` / `WcWf.nodeW_wfC_si`.

- `htkC`, `habtC`: a pc `okC` is off the take and abort sites.
- `blkW_dt`, `nodeW_dt`: a node's `SFactsSt2` at `Dt = False` at any `Dt`.
- `blkC`: a covered block returning to `L.lab rl` inside `Wf`
  (`WakeWf.blkW_wfQ` at `instOkW`).
- `nodeC`: `WcWf.nodeW_wfC_si` at a pc `okC`.
- `nodeCldop`, `nodeCst`: the counter's `ld<op>` / a header's `str` inside
  `Wf` (`WakeWf.nodeW_wfLdop` / `nodeW_wfSt` at `instOkW`).
- `reserveW_wfG`: every `ReserveW` node inside `Wf`.
- `tcbWG_wfG`: every `TcbWG` node inside `Wf`.

No absolute address appears in a statement; the proofs decide the pcs at
the certificate's labels.
-/
import Spike.Lib.A64WakeStartTcbL
import Spike.Lib.A64WakeWcResWI
import Spike.Lib.A64WakeTcb2CallW
import Spike.Lib.A64WakeWcWf

namespace Spike.Lib.A64.WakePh.CalWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.WakeWf (Wf RunWf)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS)

section Gen

variable {L : RuntimeLayout} {own : Spike.Lib.A64Consumer.Own} {a : BitVec 64} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))

omit hcl in
include hlab hsite in
/-- **A pc `okC` is off the take site.** -/
theorem htkC {pc : Int64} (h : okC pc.toBitVec.toNat = true) :
    ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → pc.toBitVec.toNat ≠ x := fun x hx => by
  rw [StartTcb.siteT hlab hsite x hx]; intro he; rw [he] at h; exact absurd h (by decide)

include hp hlo hΛ in
/-- **A pc `okC` is off the abort sites.** -/
theorem habtC {pc : Int64} (h : okC pc.toBitVec.toNat = true) :
    ∀ k x, (Spike.Lib.A64.PhRec.μ L).abortAt k = some x → pc.toBitVec.toNat ≠ x := fun j _ hx =>
  Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo, okPc_eq hΛ]; exact h)
    (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx

omit hp hlo hΛ hlab hsite hcl in
/-- A block's `SFactsSt2` at `Dt = False` holds at any `Dt`. -/
theorem blkW_dt {n : ND} {blk : List Directive}
    (h : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s) K L.exe L.endPc R F n blk) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n blk :=
  fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 => let r := h s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

omit hp hlo hΛ hlab hsite hcl in
/-- A node's `SFactsSt2` at `Dt = False` holds at any `Dt`. -/
theorem nodeW_dt {n : ND} (h : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s) K L.exe L.endPc R F n) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n :=
  fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (h s c hA).1 (fun h => h.elim), (h s c hA).2⟩

include hp hlo hΛ hlab hsite hcl

/-- **A covered block of wakeProg returning to `L.lab rl` inside `Wf`** at
the frames `fs`: its `SFactsSt2` at `Dt = False` (`hst`, moved by `K`), its pcs `okC` (`hokpc`), its abort
phases' check (`hph`, its `ret`s to `L.lab rl`, `hret`), its controls not
`main`'s `ret` at no frame with their runs well formed (`hJ`), its frames
placed (`hpl`). -/
theorem blkC {n : ND} {blk : List Directive} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt wakeProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hokpc : ∀ j < blk.length, okC (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hph : Spike.Lib.A64.WakeWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) own ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n blk := by
  have hI := instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  exact Spike.Lib.A64.WakeWf.blkW_wfQ (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := fs) hI (hp ▸ hb) he hok hR hal hlo' hhi (blkW_dt hst)
    (fun j hj s h1 h2 h3 => (hI.off s (by rw [okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokpc j hj)).1)
    (Spike.Lib.A64.WakeWf.phOffW_sound hlab hph) hret hcl hJ hpl

/-- **A silent single instruction of wakeProg inside `Wf`** at `ownG`
(`WcWf.nodeW_wfC_si` at a pc `okC`). -/
theorem nodeC {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  WcWf.nodeW_wfC_si hp hlo hlab hsite hb he hst (htkC hlab hsite hokpc) (by rw [okPc_eq hΛ]; exact hokpc) hph hcl
    hJ hpl

/-- **The counter's `ld<op>` of wakeProg inside `Wf`** (as `nodeC`): its
word unmapped in private memory (`ha`), off the arena and not its counter
word (`hoff`). -/
theorem nodeCldop {n : ND} {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) own ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  Spike.Lib.A64.WakeWf.nodeW_wfLdop (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize) (fs := fs)
    (Cl := Cl) (instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ hb) he (nodeW_dt hst)
    (htkC hlab hsite hokpc) (habtC hp hlo hΛ hokpc) (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl hJ hpl ha hoff

/-- **A header's `str` of wakeProg inside `Wf`** (as `nodeCldop`). -/
theorem nodeCst {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hokpc : okC n.pc.toBitVec.toNat = true) (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat ∧
        (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) own ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F n :=
  Spike.Lib.A64.WakeWf.nodeW_wfSt (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize) (fs := fs)
    (Cl := Cl) (instOkW hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)) (hp ▸ hb) he (nodeW_dt hst)
    (htkC hlab hsite hokpc) (habtC hp hlo hΛ hokpc) (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl hJ hpl ha hoff

open Spike.Lib.A64.Flow.Reserve (rPro rArg rBnd rJ rRet fnL entryL okL rmwPc) in
open Spike.Lib.A64.Rt.Reserve (ResG rvN ReserveW ntA) in
set_option maxHeartbeats 3200000 in
/-- **`scc_rt_thread_reserve`'s nodes inside `Wf`**, called from `wc_main`
returning to `.sp3` (`hra`), in a region with the frame `[-48, 0]`: each
node's `SFactsSt2` (`hst`) and placement (`hpl`), the control `q.c0` not
`main`'s `ret` at no frame with its runs well formed (`hc0`), the counter
`scc_rt_nthreads` unmapped under `F` (`hunN`) and off the arena and not its
counter word (`hoffN`). -/
theorem reserveW_wfG (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (q : ResG)
    (hra : q.g.ra = (L.lab ".L21_wc_main.sp3").toBitVec)
    (hc0 : (fs = [] → ∀ a, q.c0.term ≠ .ret a) ∧ RunWf p q.c0 fs)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hoffN : ¬ (ar.heap ≤ (ntA L.lab).toNat ∧ (ntA L.lab).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨ntA L.lab, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, ReserveW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F q i)
    (hpl : ∀ i, ReserveW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F q i) :
    ∀ i, ReserveW (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F q i := by
  obtain ⟨lF, lE, lO⟩ := resLabs
  have eF : (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 2165132 := hlab _ _ lF
  have eE : (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 2165148 := hlab _ _ lE
  have eO : (_root_.Executable.labels L.exe).label okL = Int64.ofNat 2165224 := hlab _ _ lO
  have hin := WcW.wake_reserveIn'
  simp only [Spike.Lib.A64.Flow.Reserve.reserveIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = q.c0) →
      ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  case e =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bE (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Reserve.rPro_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Reserve.rPro_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [okPc_eq hΛ, eF]; revert j; decide
  case entry =>
    refine nodeC hp hlo hΛ hlab hsite hcl bA (Spike.Lib.A64.Flow.ofNat4_zero _) h1 ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2
    dsimp only [rvN]; rw [eE]; decide
  case add =>
    refine nodeC hp hlo hΛ hlab hsite hcl bA1 rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
    dsimp only [rvN]; rw [eE]; decide
  case arg =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bArg rfl
      Spike.Lib.A64.Flow.Reserve.rArg_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Reserve.rArg_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [okPc_eq hΛ, eE]; revert j; decide
  case rmw =>
    refine nodeCldop hp hlo hΛ hlab hsite hcl bRmw rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
      (fun σ c m hJ' hF => ?_) (fun σ c hJ' => ?_)
    · dsimp only [rvN, rmwPc]; rw [eE]; decide
    · dsimp only [rvN] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2]; exact hunN _ hF
    · dsimp only [rvN] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2]; exact hoffN
  case bnd =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bBnd rfl
      Spike.Lib.A64.Flow.Reserve.rBnd_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Reserve.rBnd_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [okPc_eq hΛ, eE]; revert j; decide
  case j =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bJ rfl
      Spike.Lib.A64.Flow.Reserve.rJ_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Reserve.rJ_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [okPc_eq hΛ, eE]; revert j; decide
  case ok =>
    refine blkC hp hlo hΛ hlab hsite hcl (rl := ".L21_wc_main.sp3") bOk (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Reserve.rRet_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      (Spike.Lib.A64Consumer.hret_of_run Spike.Lib.A64.Flow.Reserve.rRet_ok fun σ c hJ' => ?_)
      (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [rvN]; rw [eO]; revert j; decide
    · dsimp only [rvN] at hJ' ⊢
      rw [(Spike.Lib.A64.Flow.Reserve.rRet_walk _ _ hJ'.2).1, hra]; exact Int64.ofBitVec_toBitVec _

open Spike.Lib.A64.Flow.Ret0.AllocTcb (fnL entryL lenL okL rmwPc hdrPc atPro atChk atJ1 atLen atArg atBnd atJ2
  atOk atRet) in
open Spike.Lib.A64.Rt (tcbNG TcbWG) in
set_option maxHeartbeats 3200000 in
/-- **`scc_rt_alloc_tcb`'s nodes inside `Wf`**, wake's second TCB
(`Tcb2Call.tcb2Q`) called from `wc_main` returning to `.sp4` (`hra`), in
a region with the frame `[-192, 0]`: each node's `SFactsSt2` (`hst`) and
placement (`hpl`), the control `c0` (`hc0`), the counter
`scc_rt_pinned_next` (`L.pnA`) and the header word (`L.pinA + 96`)
unmapped under `F` (`hunP`, `hunH`) and off the arena and not its counter
word (`hoffP`, `hoffH`). -/
theorem tcbWG_wfG (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (c0 : Ctl) (hra : g.ra = (L.lab ".L21_wc_main.sp4").toBitVec)
    (hc0 : (fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧ (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 96#64) 8 = none)
    (hoffH : ¬ (ar.heap ≤ (L.pinA + 96#64).toNat ∧ (L.pinA + 96#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA + 96#64, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, TcbWG (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F
      (Tcb2Call.tcb2Q g c0) i)
    (hpl : ∀ i, TcbWG (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F
      (Tcb2Call.tcb2Q g c0) i) :
    ∀ i, TcbWG (fun s c => Wf L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p Dt (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx lbl lsize s c fs) K L.exe L.endPc R F (Tcb2Call.tcb2Q g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := Tcb2W.tcb_labs hlab (L := L)
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have hin := Tcb2W.wake_allocTcbIn
  simp only [Spike.Lib.A64.Flow.Ret0.AllocTcb.allocTcbIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = c0) →
      ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [TcbWG] at h1 h2 ⊢
  case e =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bE (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atPro_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atPro_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eFn]; revert j; decide
  case entry =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bEn (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atChk_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atChk_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eEn]; revert j; decide
  case j1 =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bJ1 rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atJ1_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atJ1_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eEn]; revert j; decide
  case len =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bLen (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atLen_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atLen_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eLen]; revert j; decide
  case adrp =>
    refine nodeC hp hlo hΛ hlab hsite hcl bA rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
    dsimp only [tcbNG]; rw [eLen]; decide
  case add =>
    refine nodeC hp hlo hΛ hlab hsite hcl bA1 rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
    dsimp only [tcbNG]; rw [eLen]; decide
  case arg =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bArg rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atArg_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atArg_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eLen]; revert j; decide
  case rmw =>
    refine nodeCldop hp hlo hΛ hlab hsite hcl bRmw rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
      (fun σ c m hJ' hF => ?_) (fun σ c hJ' => ?_)
    · dsimp only [tcbNG, rmwPc]; rw [eLen]; decide
    · dsimp only [tcbNG] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2, hpn]; exact hunP _ hF
    · dsimp only [tcbNG] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2, hpn]; exact hoffP
  case bnd =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bBnd rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atBnd_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atBnd_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eLen]; revert j; decide
  case j2 =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bJ2 rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atJ2_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atJ2_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eLen]; revert j; decide
  case ok =>
    refine nodeC hp hlo hΛ hlab hsite hcl bO (Spike.Lib.A64.Flow.ofNat4_zero _) h1 ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2
    dsimp only [tcbNG]; rw [eOk]; decide
  case ok1 =>
    refine nodeC hp hlo hΛ hlab hsite hcl bO1 rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
    dsimp only [tcbNG]; rw [eOk]; decide
  case ok2 =>
    refine WcWf.blkW_wfC hp hlo hlab hsite bO2 rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atOk_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      Spike.Lib.A64.Rt.Tcb.atOk_noRet hcl (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [okPc_eq hΛ, eOk]; revert j; decide
  case hdr =>
    refine nodeCst hp hlo hΛ hlab hsite hcl bH rfl h1 ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2
      (fun σ c m hJ' hF => ?_) (fun σ c m hJ' hF => ?_)
    · dsimp only [tcbNG, hdrPc]; rw [eOk]; decide
    · dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]
      rw [hJ'.2.2.2, Tcb2Call.tcb2Q_hdrA, hpin]; exact hunH _ hF
    · dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]
      rw [hJ'.2.2.2, Tcb2Call.tcb2Q_hdrA, hpin]; exact hoffH
  case ret =>
    refine blkC hp hlo hΛ hlab hsite hcl (rl := ".L21_wc_main.sp4") bRet rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atRet_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      (Spike.Lib.A64Consumer.hret_of_run Spike.Lib.A64.Flow.Ret0.AllocTcb.atRet_ok fun σ c hJ' => ?_)
      (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [tcbNG]; rw [eOk]; revert j; decide
    · dsimp only [tcbNG] at hJ' ⊢
      rw [(Spike.Lib.A64.Flow.Ret0.AllocTcb.atRet_walkG _ _ hJ'.2).1]; show Int64.ofBitVec g.ra = _; rw [hra]; exact Int64.ofBitVec_toBitVec _

end Gen

end Spike.Lib.A64.WakePh.CalWf

/-- info: 'Spike.Lib.A64.WakePh.CalWf.blkC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.blkC

/-- info: 'Spike.Lib.A64.WakePh.CalWf.nodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.nodeC

/-- info: 'Spike.Lib.A64.WakePh.CalWf.reserveW_wfG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.reserveW_wfG

/-- info: 'Spike.Lib.A64.WakePh.CalWf.tcbWG_wfG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.CalWf.tcbWG_wfG
