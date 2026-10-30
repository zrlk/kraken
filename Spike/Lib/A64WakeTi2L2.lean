/-
**The second `scc_rt_stack_take` call's lock nodes and take site inside
`W0`** (AArch64; the `hatA` ti discharger): the lock's swap, the free
count's load, the lock's release and the take site of the call from the
second `scc_rt_thread_init` (on a pool stack) inside the level
`StartWf.WS`, as `StartTi.nodeI_WSswp` … `siteI_WS` with the frame on the
pool (`Ti2.BandP`) and `ownG` at `own2b` (`Ti2.node2_own`, `site2_own`).

- `node2_WSswp`, `node2_WSldr`, `node2_WSstlr`: the swap, the load and the
  release inside `WS`.
- `site2_WS`: the take site inside `WS`.
-/
import Spike.Lib.A64WakeTi2L
import Spike.Lib.A64WakeStartTiL2

namespace Spike.Lib.A64.WakePh.StartTi

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakeWf (RunWf swpDir stlrDir)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib (Arena FragS)
open Spike.Lib.A64.WakePh.Ti2 (BandP node2_own site2_own)

section Gen

variable {L : RuntimeLayout} {Pl : MachineData → Prop} {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl}
  {K : State → State → Prop} {R : Spike.Lib.Region} {F : MachineData → Prop} {klo : Int}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s : State, Pl s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hPl : ∀ m m', F m → Spike.Lib.A64.Flow.DFrame R m m' → Pl m')
  (hX0 : ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
    pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat → X0 s)
  (hbd : BandP L R klo)

include hp hlo hlab hsite hcl hc0 hpl0 hPl hX0 hbd

/-- **The lock's swap inside `WS`** (as `node2_WS`): `swp<k> Xs, Xt, [Xn]`
of a word unmapped in private memory (`ha`), off the arena and not the
counter word (`hoff`). -/
theorem node2_WSswp {n : ND} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [swpDir kk rs rt b] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcN n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfSwp (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The free count's load inside `WS`** (as `node2_WS`): `ldr Xt, [Xn, #i]`
of a word unmapped in private memory (`ha`). -/
theorem node2_WSldr {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [Spike.Lib.A64.Flow.ldrDir t b i] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcN n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfLdr (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)), fun _ h => h⟩) ha
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The lock's release inside `WS`** (as `node2_WS`): `stlr Xt, [Xn]` of a
word unmapped in private memory (`ha`), off the arena and not the counter
word (`hoff`). -/
theorem node2_WSstlr {n : ND} {t b : XReg} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [stlrDir t b] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hokpc : okPcOf lo wakeProg L.Λ (L.lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcN n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c →
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧ (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc) :
    NodeW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  rw [he] at hokpc
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.nodeW_wfStlr (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) hI (hp ▸ hb) he (node2_own (Dt := Dt) hlab hbd hS hk ⟨hpc.1.1, hpc.2⟩ hso)
    (tkI (StartTcb.siteT hlab hsite) hpc.1)
    (fun j x hx => Spike.Lib.A64.PhRec.ne_of_okPcOf (by rw [hp, hlo]; exact hokpc)
      (by cases j <;> simp [Scc.Cert.Rt.A64.siteLabels]) hx)
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact ⟨hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)), fun _ h => h⟩) ha hoff
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_ hw
  rintro s c ⟨_, _, _, hpc', _⟩
  exact ⟨hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1.1)) (offSite hlab (by rw [hpc']; exact hpc.1)), fun _ h => h⟩

/-- **The take site inside `WS`**: the `nop` (`hb`), its states' `SFactsSt` at
the second instance (`hS`), off the abort sites (`habt`), its successors
keeping `sp` and `x30` 4 bytes on (`hk`), its pc and the next in the
callees (`hpc`), its static `sp` offset in `[klo, 0]` (`hso`), its abort
phases' check (`hph`), its controls `c0` (`hJ`); `X0` at the site's states
from their take range, frame and region cells (`hXs`), off it by `hX0`. -/
theorem site2_WS {n : ND} {l : Label} {k : Nat}
    (hb : blockAt wakeProg l k [.instr ⟨.W64, .NOP⟩] = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
    (habt : ∀ k x, (Spike.Lib.A64.PhRec.μ L).abortAt k = some x → n.pc.toBitVec.toNat ≠ x)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0)
    (hph : Spike.Lib.A64.WakeWf.siOffW pfxM l k = true) (hJ : ∀ σ c, n.J σ c → c = c0)
    (hXs : ∀ s, pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = rS → F s.st.1 →
      (∀ k, R.Off k → (Mem.loadInt s.st.1.dmem (R.addr k) 8).isSome) → X0 s) :
    ∀ s c, At L.exe L.endPc R F n s c → WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := rS)
  have hw := Spike.Lib.A64.WakeWf.site_wf (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
    (fs := []) (Cl := Cl) (Dt := Dt) hI (hp ▸ hb) he (site2_own hlab hbd hS hk hpc hso) habt
    (Spike.Lib.A64.WakeWf.siOffW_sound hlab hph) hcl
    (fun σ c hJ' => by rw [hJ σ c hJ']; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (fun s c ⟨_, _, _, _, σ, _, hF, hJ'⟩ => by
      rw [hJ σ c hJ']; exact hpl0 _ (hPl _ _ hF (Spike.Lib.A64.Flow.DFrame.refl _ _)))
  intro s c hA
  have hpc' := hA.2.2.2.1
  have hx : X0 s := by
    by_cases hs : pcOf s = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat
    · obtain ⟨-, -, -, -, σ, hAb, hF, -⟩ := id hA
      refine hXs s hs ((hS s c hA).site _ hsite hs).2.2.2.1 hF fun k hk => ?_
      obtain ⟨j, hj, -⟩ := hAb.slot k hk
      rw [hj]; rfl
    · exact hX0 _ (inI_of hlab (by rw [hpc']; exact hpc.1)) hs
  exact ⟨.inl rfl, hx, hw s c hA⟩

end Gen

/-- info: 'Spike.Lib.A64.WakePh.StartTi.node2_WSswp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node2_WSswp

/-- info: 'Spike.Lib.A64.WakePh.StartTi.node2_WSldr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node2_WSldr

/-- info: 'Spike.Lib.A64.WakePh.StartTi.node2_WSstlr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms node2_WSstlr

/-- info: 'Spike.Lib.A64.WakePh.StartTi.site2_WS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms site2_WS

end Spike.Lib.A64.WakePh.StartTi
