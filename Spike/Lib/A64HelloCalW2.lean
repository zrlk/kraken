/-
**hello.w's `wc_main` callees inside the root's third level `RootWX.W2H`** (AArch64; rows hP-res, hP-tcb;
the twin of `Spike/Lib/A64WakeWfCal.lean` at helloProg, frame 144): the nodes of `scc_rt_thread_reserve`
(`ReserveW`, returning to `.sp3`) and of the second `scc_rt_alloc_tcb` (`TcbWG`, returning to `.sp4`) inside
`W2H L (ntA L.lab) ar helloSrc Dt (ClH L) Ctx lbl lsize` at no frames and no outside moves, from each node's
`SFactsSt2` at `ownGH L (ntA L.lab)` (`hst`, at any move) and placement (`hpl`), the callee's control (`hc0`), and
the written words unmapped under `F` and off the arena (`hun*`, `hoff*`).

- `blkC_W2H`: a covered block returning to `L.lab rl` (`HelloWf.blkW_wfQH` at `instOkH`).
- `nodeC_W2H`: a silent single instruction (`WcWf.nodeW_wfC_siH`).
- `nodeCldop_W2H`, `nodeCst_W2H`: the counter's `ld<op>`, a header's `str` (`HelloWf.nodeW_wfLdopH`,
  `nodeW_wfStH`).
- `reserveW_W2H`: every `ReserveW` node inside `W2H`.
- `tcbWG_W2H`: every `TcbWG` node of `tcb2QH` inside `W2H`.

The pcs are decided at the canonical base (`hlab`); no absolute address appears in a statement.
-/
import Spike.Lib.A64HelloWcW2
import Spike.Lib.A64WakeWfCal

namespace Spike.Lib.A64.HelloPh.CalW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.HelloPh.RootWX (W2H)
open Spike.Lib.A64.HelloPh.WcW2 (blkW_W2H blkW_noKH nodeW_noKH htk_ofC)
open Spike.Lib.A64.Flow.HelloWc (tcb2QH tcb2QH_hdrA)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.HelloSrc (helloSrc)

section Gen

variable {L : RuntimeLayout} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {K : State → State → Prop} {R : Region} {F : MachineData → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at no frames. -/
local notation "W2" => fun s c => W2H L (ntA L.lab) ar helloSrc Dt (Spike.Lib.A64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

/-- **A covered block returning to `L.lab rl` inside `W2H`** at no move (`HelloWf.blkW_wfQH` at `instOkH`): its
`SFactsSt2` at `ownGH L (ntA L.lab)` (`hst`, at any move), its pcs `okC` (`hokP`), its abort phases' check (`hph`,
its `ret`s to `L.lab rl`, `hret`), its controls not at a `ret` with their runs well formed (`hJ`), its frames
placed (`hpl`). -/
theorem blkC_W2H {n : ND} {blk : List Directive} {l rl : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc R F
      n blk)
    (hokP : ∀ j < blk.length, Spike.Lib.A64.HelloPh.okC (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true)
    (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = L.lab rl)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW W2 (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hI := Spike.Lib.A64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hW := Spike.Lib.A64.HelloWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Dt := Dt) (Cl := Spike.Lib.A64.HelloPh.ClH L) (lbl := lbl) (pfx := pfxM) hI (hp ▸ hb) he hok hR hal
    hlo' hhi (Spike.Lib.A64.WakePh.CalWf.blkW_dt hst)
    (fun j hj s _ _ h3 => (hI.off s (by
      rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ]; unfold pcOf; rw [h3]; exact hokP j hj)).1)
    (Spike.Lib.A64.HelloWf.phOffHC_sound hlab hph) hret (fun _ h => h.2)
    (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
  exact blkW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **A silent single instruction inside `W2H`** at no move (`WcWf.nodeW_wfC_siH`): its pc off the take site
(`htk`) and `okC` (`hokP`). -/
theorem nodeC_W2H {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.A64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hW := Spike.Lib.A64.HelloPh.WcWf.nodeW_wfC_siH (Dt := Dt) (ar := ar) (p := helloSrc)
    (Cl := Spike.Lib.A64.HelloPh.ClH L) (Ctx := Ctx) (lsize := lsize) (fs := []) hp hlo hlab hsite hb he hst htk
    (by rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ]; exact hokP) hph (fun _ h => h.2)
    (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **The counter's `ld<op>` inside `W2H`** (as `nodeC_W2H`): its word unmapped in private memory (`ha`), off the
arena and not its counter word (`hoff`). -/
theorem nodeCldop_W2H {n : ND} {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.A64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := Spike.Lib.A64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hok : okPcOf lo SccCode.helloProg L.Λ n.pc.toBitVec.toNat = true := by
    rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ]; exact hokP
  have hW := Spike.Lib.A64.HelloWf.nodeW_wfLdopH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
    (lsize := lsize) (fs := []) (Dt := Dt) (pfx := pfxM) (Cl := Spike.Lib.A64.HelloPh.ClH L) (lbl := lbl) hI
    (hp ▸ hb) he (Spike.Lib.A64.WakePh.CalWf.nodeW_dt hst) htk
    (Spike.Lib.A64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hok) (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph)
    (fun _ h => h.2) (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl ha hoff
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

/-- **A header's `str` inside `W2H`** (as `nodeCldop_W2H`). -/
theorem nodeCst_W2H {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc R F n)
    (htk : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → n.pc.toBitVec.toNat ≠ x)
    (hokP : Spike.Lib.A64.HelloPh.okC n.pc.toBitVec.toNat = true)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c m, n.J σ c → F m →
      ¬ (ar.heap ≤ (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat ∧
        (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW W2 (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := Spike.Lib.A64.HelloPh.instOkH hp hlo (ntA L.lab) (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hok : okPcOf lo SccCode.helloProg L.Λ n.pc.toBitVec.toNat = true := by
    rw [Spike.Lib.A64.HelloPh.okPc_eq hΛ]; exact hokP
  have hW := Spike.Lib.A64.HelloWf.nodeW_wfStH (Λ := L.Λ) (ar := ar) (p := helloSrc) (Ctx := Ctx)
    (lsize := lsize) (fs := []) (Dt := Dt) (pfx := pfxM) (Cl := Spike.Lib.A64.HelloPh.ClH L) (lbl := lbl) hI
    (hp ▸ hb) he (Spike.Lib.A64.WakePh.CalWf.nodeW_dt hst) htk
    (Spike.Lib.A64.HelloPh.WcWf.habt_of_okPcOfH hp hlo hok) (Spike.Lib.A64.HelloWf.siOffHC_sound hlab hph)
    (fun _ h => h.2) (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl ha hoff
  exact nodeW_noKH hW fun _ _ h => ⟨rfl, h⟩

open Spike.Lib.A64.Flow.Reserve (rPro rArg rBnd rJ rRet fnL entryL okL rmwPc) in
open Spike.Lib.A64.Rt.Reserve (ResG rvN ReserveW) in
set_option maxHeartbeats 3200000 in
/-- (row hP-res) **`scc_rt_thread_reserve`'s nodes inside `W2H`**, called from `wc_main` returning to `.sp3`
(`hra`), in a region with the frame `[-48, 0]`, at no move: each node's `SFactsSt2` (`hst`, at any move) and
placement (`hpl`), the control `q.c0` not at a `ret` with its runs well formed (`hc0`), the counter
`scc_rt_nthreads` unmapped under `F` (`hunN`) and off the arena and not its counter word (`hoffN`). -/
theorem reserveW_W2H (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (q : ResG)
    (hra : q.g.ra = (L.lab ".L22_wc_main.sp3").toBitVec)
    (hc0 : (∀ a, q.c0.term ≠ .ret a) ∧ RunWf helloSrc q.c0 [])
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hoffN : ¬ (ar.heap ≤ (ntA L.lab).toNat ∧ (ntA L.lab).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨ntA L.lab, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, ReserveW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe
      L.endPc R F q i)
    (hpl : ∀ i, ReserveW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F q i) :
    ∀ i, ReserveW W2 (fun _ _ => False) L.exe L.endPc R F q i := by
  obtain ⟨lF, lE, lO⟩ := Spike.Lib.A64.HelloPh.resLabs
  have eF : (_root_.Executable.labels L.exe).label fnL = Int64.ofNat 2165168 := hlab _ _ lF
  have eE : (_root_.Executable.labels L.exe).label entryL = Int64.ofNat 2165184 := hlab _ _ lE
  have eO : (_root_.Executable.labels L.exe).label okL = Int64.ofNat 2165260 := hlab _ _ lO
  have hin := Spike.Lib.A64.Flow.HelloWc.hello_reserveIn
  simp only [Spike.Lib.A64.Flow.Reserve.reserveIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = q.c0) →
      ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [] :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [ReserveW] at h1 h2 ⊢
  case e =>
    refine blkW_W2H hp hlo hΛ hlab hsite bE (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Reserve.rPro_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [eF]; revert j; decide
  case entry =>
    refine nodeC_W2H hp hlo hΛ hlab hsite bA (Spike.Lib.A64.Flow.ofNat4_zero _) h1
      (htk_ofC hlab hsite ?_) ?_ (by decide +kernel) (hJ _ fun _ _ h => h.1) h2 <;>
      (dsimp only [rvN]; rw [eE]; decide)
  case add =>
    refine nodeC_W2H hp hlo hΛ hlab hsite bA1 rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 <;> (dsimp only [rvN]; rw [eE]; decide)
  case arg =>
    refine blkW_W2H hp hlo hΛ hlab hsite bArg rfl
      Spike.Lib.A64.Flow.Reserve.rArg_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [eE]; revert j; decide
  case rmw =>
    refine nodeCldop_W2H hp hlo hΛ hlab hsite bRmw rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 (fun σ c m hJ' hF => ?_) (fun σ c hJ' => ?_)
    · dsimp only [rvN, rmwPc]; rw [eE]; decide
    · dsimp only [rvN, rmwPc]; rw [eE]; decide
    · dsimp only [rvN] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2]; exact hunN _ hF
    · dsimp only [rvN] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2]; exact hoffN
  case bnd =>
    refine blkW_W2H hp hlo hΛ hlab hsite bBnd rfl
      Spike.Lib.A64.Flow.Reserve.rBnd_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [eE]; revert j; decide
  case j =>
    refine blkW_W2H hp hlo hΛ hlab hsite bJ rfl
      Spike.Lib.A64.Flow.Reserve.rJ_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [rvN]; rw [eE]; revert j; decide
  case ok =>
    refine blkC_W2H hp hlo hΛ hlab hsite (rl := ".L22_wc_main.sp3") bOk (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Reserve.rRet_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      (Spike.Lib.A64Consumer.hret_of_run Spike.Lib.A64.Flow.Reserve.rRet_ok fun σ c hJ' => ?_)
      (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [rvN]; rw [eO]; revert j; decide
    · dsimp only [rvN] at hJ' ⊢
      rw [(Spike.Lib.A64.Flow.Reserve.rRet_walk _ _ hJ'.2).1, hra]; exact Int64.ofBitVec_toBitVec _

open Spike.Lib.A64.Flow.Ret0.AllocTcb (fnL entryL lenL okL rmwPc hdrPc) in
open Spike.Lib.A64.Rt (tcbNG TcbWG) in
set_option maxHeartbeats 3200000 in
/-- (row hP-tcb) **The second `scc_rt_alloc_tcb`'s nodes inside `W2H`** (`tcb2QH`, called from `wc_main` returning
to `.sp4`, `hra`), in a region with the frame `[-192, 0]`, at no move: each node's `SFactsSt2` (`hst`, at any move)
and placement (`hpl`), the control `c0` (`hc0`), the counter `scc_rt_pinned_next` (`L.pnA`) and the header word
(`L.pinA + 104`) unmapped under `F` (`hunP`, `hunH`) and off the arena and not its counter word (`hoffP`,
`hoffH`). -/
theorem tcbWG_W2H (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (g : Spike.Lib.A64.Flow.Ret0.AllocTcb.G) (c0 : Ctl) (hra : g.ra = (L.lab ".L22_wc_main.sp4").toBitVec)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf helloSrc c0 [])
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧ (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hoffH : ¬ (ar.heap ≤ (L.pinA + 104#64).toNat ∧ (L.pinA + 104#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA + 104#64, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hst : ∀ i, TcbWG (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L (ntA L.lab)) s) K L.exe L.endPc
      R F (tcb2QH g c0) i)
    (hpl : ∀ i, TcbWG (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F (tcb2QH g c0) i) :
    ∀ i, TcbWG W2 (fun _ _ => False) L.exe L.endPc R F (tcb2QH g c0) i := by
  obtain ⟨eFn, eEn, eLen, eOk, -, -⟩ := Spike.Lib.A64.HelloPh.Tcb2W.tcb_labsH hlab (L := L)
  have hpn : Spike.Lib.A64.Flow.Ret0.pnA L.lab = L.pnA := L.lab_pn
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA L.lab = L.pinA := L.lab_pin
  have hin := Spike.Lib.A64.Flow.HelloWc.hello_allocTcbIn
  simp only [Spike.Lib.A64.Flow.Ret0.AllocTcb.allocTcbIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := hin
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = c0) →
      ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf helloSrc c [] :=
    fun _ hn σ c h => by rw [hn σ c h]; exact hc0
  intro i
  have h1 := hst i
  have h2 := hpl i
  cases i <;> dsimp only [TcbWG] at h1 h2 ⊢
  case e =>
    refine blkW_W2H hp hlo hΛ hlab hsite bE (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atPro_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eFn]; revert j; decide
  case entry =>
    refine blkW_W2H hp hlo hΛ hlab hsite bEn (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atChk_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eEn]; revert j; decide
  case j1 =>
    refine blkW_W2H hp hlo hΛ hlab hsite bJ1 rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atJ1_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eEn]; revert j; decide
  case len =>
    refine blkW_W2H hp hlo hΛ hlab hsite bLen (Spike.Lib.A64.Flow.ofNat4_zero _)
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atLen_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eLen]; revert j; decide
  case adrp =>
    refine nodeC_W2H hp hlo hΛ hlab hsite bA rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 <;> (dsimp only [tcbNG]; rw [eLen]; decide)
  case add =>
    refine nodeC_W2H hp hlo hΛ hlab hsite bA1 rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 <;> (dsimp only [tcbNG]; rw [eLen]; decide)
  case arg =>
    refine blkW_W2H hp hlo hΛ hlab hsite bArg rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atArg_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eLen]; revert j; decide
  case rmw =>
    refine nodeCldop_W2H hp hlo hΛ hlab hsite bRmw rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 (fun σ c m hJ' hF => ?_) (fun σ c hJ' => ?_)
    · dsimp only [tcbNG, rmwPc]; rw [eLen]; decide
    · dsimp only [tcbNG, rmwPc]; rw [eLen]; decide
    · dsimp only [tcbNG] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2, hpn]; exact hunP _ hF
    · dsimp only [tcbNG] at hJ'; simp only [Reg64s.getXReg]; rw [hJ'.2.2.2, hpn]; exact hoffP
  case bnd =>
    refine blkW_W2H hp hlo hΛ hlab hsite bBnd rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atBnd_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eLen]; revert j; decide
  case j2 =>
    refine blkW_W2H hp hlo hΛ hlab hsite bJ2 rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atJ2_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eLen]; revert j; decide
  case ok =>
    refine nodeC_W2H hp hlo hΛ hlab hsite bO (Spike.Lib.A64.Flow.ofNat4_zero _) h1 (htk_ofC hlab hsite ?_) ?_
      (by decide +kernel) (hJ _ fun _ _ h => h.1) h2 <;> (dsimp only [tcbNG]; rw [eOk]; decide)
  case ok1 =>
    refine nodeC_W2H hp hlo hΛ hlab hsite bO1 rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 <;> (dsimp only [tcbNG]; rw [eOk]; decide)
  case ok2 =>
    refine blkW_W2H hp hlo hΛ hlab hsite bO2 rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atOk_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel) (by decide)
      (hJ _ fun _ _ h => h.1) h2
    intro j hj; dsimp only [tcbNG]; rw [eOk]; revert j; decide
  case hdr =>
    refine nodeCst_W2H hp hlo hΛ hlab hsite bH rfl h1 (htk_ofC hlab hsite ?_) ?_ (by decide +kernel)
      (hJ _ fun _ _ h => h.1) h2 (fun σ c m hJ' hF => ?_) (fun σ c m hJ' hF => ?_)
    · dsimp only [tcbNG, hdrPc]; rw [eOk]; decide
    · dsimp only [tcbNG, hdrPc]; rw [eOk]; decide
    · dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]
      rw [hJ'.2.2.2, tcb2QH_hdrA, hpin]; exact hunH _ hF
    · dsimp only [tcbNG] at hJ'
      rw [Spike.Lib.A64.Rt.Tcb.rAddr_zero]; simp only [Reg64s.getXReg]
      rw [hJ'.2.2.2, tcb2QH_hdrA, hpin]; exact hoffH
  case ret =>
    refine blkC_W2H hp hlo hΛ hlab hsite (rl := ".L22_wc_main.sp4") bRet rfl
      Spike.Lib.A64.Flow.Ret0.AllocTcb.atRet_ok hR hal (by omega) (by omega) h1 ?_ (by decide +kernel)
      (Spike.Lib.A64Consumer.hret_of_run Spike.Lib.A64.Flow.Ret0.AllocTcb.atRet_ok fun σ c hJ' => ?_)
      (hJ _ fun _ _ h => h.1) h2
    · intro j hj; dsimp only [tcbNG]; rw [eOk]; revert j; decide
    · dsimp only [tcbNG] at hJ' ⊢
      rw [(Spike.Lib.A64.Flow.Ret0.AllocTcb.atRet_walkG _ _ hJ'.2).1]; show Int64.ofBitVec g.ra = _
      rw [hra]; exact Int64.ofBitVec_toBitVec _

end Gen

end Spike.Lib.A64.HelloPh.CalW2

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.CalW2.blkC_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalW2.blkC_W2H

/-- info: 'Spike.Lib.A64.HelloPh.CalW2.nodeC_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalW2.nodeC_W2H

/-- info: 'Spike.Lib.A64.HelloPh.CalW2.nodeCldop_W2H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalW2.nodeCldop_W2H

/-- info: 'Spike.Lib.A64.HelloPh.CalW2.nodeCst_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalW2.nodeCst_W2H

/-- info: 'Spike.Lib.A64.HelloPh.CalW2.reserveW_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalW2.reserveW_W2H

/-- info: 'Spike.Lib.A64.HelloPh.CalW2.tcbWG_W2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.CalW2.tcbWG_W2H
