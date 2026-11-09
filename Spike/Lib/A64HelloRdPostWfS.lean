/-
**hello.w's `wc_rodata` from the allocator's return, and `scc_rt_main`'s `.sp0`
block, inside the start's level `WSH`** (AArch64; the
`WSH` twin of `A64HelloRdPostWI`): `HelloRd.RdPostW` and `HelloM.MainPostW.sp0`
at `StartWf.WSH` (`W0` at the frames `[]` at `ownGH`), moved only by the take
(`PhRec.K L rS`). Each node is `HelloWf.blkW_wfQH` (a block, its `ret`s to
`L.lab rl`) or `WcWf.nodeW_wfCH` at its `SFactsSt2` (`WcW.rdPostW_wcGH`,
`WcW.mB1W_wcGH`), `X0` from its free pcs (`hX0`). Generic in the layout `L`, the
region `R`, the source, the arena and the level.

- `blkW_rpWSH`, `nodeW_rpWSH`: a block (its `ret`s to `L.lab rl`), a single
  instruction of `rpTabH` inside `WSH`.
- `ld_stepH`: a load of a word unmapped under `F` steps to `pc + 4` and writes
  nothing.
- `rdPostW_WSH`: `RdPostW` inside `WSH`: `rdPostW_wcGH`'s premises (`hbuf`,
  `hra`), the controls' facts at every invariant (`hcf`), the frames placed
  per node (`hpl`), the two stores' writes' obligations (`hwr1`, `hwr2`).
- `mB1W_WSH`: the `.sp0` block of `scc_rt_main` inside `WSH`.
-/
import Spike.Lib.A64HelloRdPostWI
import Spike.Lib.A64HelloRdWfS

namespace Spike.Lib.A64.HelloPh.RdWfS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (PhFact blockAt okPcOf codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero)
open Spike.Lib.A64.WakeWf (RunWf NoWrC)
open Spike.Lib.A64.HelloPh.WcW (freeNH freeAtH freeAt_pcH freeAt_pc0H rpTabH rpW_factH BoxOkH cell1H)
open Spike.Lib.A64.HelloPh.StartWf (WSH)
open Spike.Lib.A64.Flow.HelloRd (pN RdPostW rpIn hello_rpIn)
open Spike.Lib.A64.Flow.Hello1 (rpB0 rpB0_ok rpB1 rpB1_ok rpB2 rpB2_ok rpB3 rpB3_ok rpB4 rpB4_ok rpB4_run
  rAddr_x10_x0 mB1 mB1_ok mS0)
open Spike.Lib.A64.Flow.WakeWc (pubF_eq)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib (Arena FragS)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-! ## A block and a node inside `WSH` -/

/-- **A covered block of `rpTabH` inside `WSH`**, its `ret`s to `L.lab rl`
(`hret`; `rl` the fact's return label, `hra`): its `SFactsSt2` at `ownGH`
(`hst`), its abort phases' check (`hph`), its pcs free (`hfree`), its controls'
facts (`hJ`), its frames placed (`hpl`). -/
theorem blkW_rpWSH {n : ND} {blk : List Directive} {l rl : Label} {k : Nat} {blo bhi : Int} {ra : Option String}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH) (hra : ∀ r, ra = some r → L.lab rl = L.lab r)
    (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed =
        L.lab rl)
    (hfree : freeAtH l k blk.length = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := L.lab rl) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (rpW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo SccCode.helloProg L.Λ (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.HelloWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
      (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst'
      (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
      (Spike.Lib.A64.HelloWf.phOffHC_sound hlab hph) hret hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  have := freeAt_pcH hlab hfree hj
  rw [he] at this
  exact this

/-- **`blkW_rpWSH` across a return label**: the block's `blk.take jA` ends at
label `m` and `blk.drop jA` follows it (`blockAcross`); via `blkW_wfQHA`. -/
theorem blkW_rpWSHA {n : ND} {blk : List Directive} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    {ra : Option String}
    (hb : Scc.Cert.Rt.A64.blockAcross SccCode.helloProg l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH) (hra : ∀ r, ra = some r → L.lab rl = L.lab r)
    (hph : Spike.Lib.A64.HelloWf.phOffHC pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed =
        L.lab rl)
    (hfree : freeAtH l k blk.length = true)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := L.lab rl) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (rpW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo SccCode.helloProg L.Λ (n.pc + Int64.ofNat (4 * j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  refine Spike.Lib.A64.WakeWf.blkW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.HelloWf.blkW_wfQHA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
      (fs := []) hI (hp ▸ hb) he hok hR hal hlo' hhi hst'
      (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
      (Spike.Lib.A64.HelloWf.phOffHC_sound hlab hph) hret hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  have := freeAt_pcH hlab hfree hj
  rw [he] at this
  exact this

/-- **A single instruction of `rpTabH` without an event inside `WSH`**
(`nodeW_rdWSH` at `rpTabH`). -/
theorem nodeW_rpWSH {n : ND} {l : Label} {k : Nat} (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) K L.exe L.endPc R F n)
    (hfree : freeAtH l k 1 = true) (hf : PhFact.step l k ∈ rpTabH)
    (hph : Spike.Lib.A64.HelloWf.siOffHC pfxM l k = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4)
    (hJ : ∀ σ c, n.J σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F n := by
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by rw [← he]; exact freeAt_pc0H hlab hfree
  have hok := (Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab (rpW_factH hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.A64.WakeWf.nodeW_w0 (.inl rfl) ?_
    (Spike.Lib.A64.HelloPh.WcWf.nodeW_wfCH (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.A64.HelloPh.WcWf.htk_of_freeNH hlab hsite hf0) hok hph hstep hcl
      (fun σ c h => ⟨fun _ => (hJ σ c h).1, (hJ σ c h).2⟩) hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

omit hlo hΛ hlab hsite hcl hX0 in
/-- **A load `ldr Xt, [Xn, #i]` of a word unmapped under `F`** (`ha`) steps to
`pc + 4` and writes nothing. -/
theorem ld_stepH {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat}
    (hb : blockAt SccCode.helloProg l k [Spike.Lib.A64.Flow.ldrDir t b i] = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none) :
    (∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.A64.CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s' : State, Scc.Sem.TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) ∧
    NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F n := by
  have key : ∀ s c, At L.exe L.endPc R F n s c → ∃ hc : Kraken.Promising.Lower.A64.CellAt s
      (Spike.Lib.A64.Flow.ldrDir t b i) 4, isaLSE2.exec s = some (.load .plain false
        ⟨Spike.Lib.A64.Flow.rAddr s.st.1.regs b i, 8⟩ fun v => .done (Kraken.Promising.Lower.A64.after s 4
          { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })) := by
    rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hF, hJ⟩
    have hc := cell1H hp hb hs hn (by rw [hpc, he])
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
    exact ⟨hc, Kraken.Promising.Lower.A64.exec_ldr_agrees hc rfl (ha' ▸ ha σ c s.st.1 hJ hF)
      (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)⟩
  refine ⟨fun s c hA => ?_, Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA =>
    let ⟨_, hx⟩ := key s c hA; ⟨Spike.Lib.A64ConsumerA.noWr_load hx, fun _ h => h⟩⟩
  obtain ⟨hc, hx⟩ := key s c hA
  refine ⟨_, _, hc, fun imm h => by simp [Spike.Lib.A64.Flow.ldrDir] at h, hx, fun s' hu => ?_⟩
  obtain ⟨_, hu⟩ := hu
  simp only [Scc.Sem.TreeLeaf] at hu
  subst hu; rfl

/-! ## `wc_rodata` from the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`RdPostW` inside `WSH`**, moved only by the take: `rdPostW_wcGH`'s
premises (the buffer's two words `BoxOkH` at every `.sp0` state, `hbuf`; the
saved return address `scc_rt_main`'s `.sp0`, `hra`), the controls' facts at
every invariant (`hcf`), the frames placed per node (`hpl`), the two
exchanges' stores' writes' obligations (`hwr1`, `hwr2`). -/
theorem rdPostW_WSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 J5 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      BoxOkH L.Λ L a F (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 i))
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot (-8) = (L.lab ".L1_scc_rt_main.sp0").toBitVec)
    (hcf : ∀ σ0 c, (Jp σ0 c ∨ Jp' σ0 c ∨ J1 σ0 c ∨ J2 σ0 c ∨ J2' σ0 c ∨ J3 σ0 c ∨ J4 σ0 c ∨ J5 σ0 c) →
      (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : RdPostW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F
      Jp Jp' J1 J2 J2' J3 J4 J5)
    (hwr1 : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .x1))
    (hwr2 : NodeW (NoWrC ar p lbl lsize Ctx []) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .x2)) :
    RdPostW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      Jp Jp' J1 J2 J2' J3 J4 J5 := by
  have hS := Spike.Lib.A64.HelloPh.WcW.rdPostW_wcGH (Λ := L.Λ) (rS := rS) (Jp' := Jp') (J1 := J1) (J2 := J2)
    (J2' := J2') (J3 := J3) (J4 := J4) (J5 := J5) hp hlo hΛ hlab hsite a hR hal hRlo hhi hbuf hra
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨b0, bl1⟩, b1⟩, bx1⟩, b2⟩, bl2⟩, b3⟩, bx2⟩, bf⟩, b4⟩ := hin
  rw [pubF_eq] at bf
  have nr : ∀ {blk : List Directive}, Spike.Lib.A64Consumer.noRetBlk blk = true → ∀ {n : ND} {x : Int64},
      ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = x :=
    fun hnr _ _ _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hnr j hj r hr).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (rl := ".L19_wc_rodata.sp0") (k := 0) (ra := none) b0
      (ofNat4_zero _) rpB0_ok hR hal hRlo hhi hS.s0 (by decide) (fun _ h => by cases h) (by decide +kernel)
      (nr (by decide)) (by free_decH) (fun σ c h => hcf σ c (.inl h)) hpl.s0
  · have h := ld_stepH (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (R := R) hp
      (n := pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .l1) (k := 2) bl1 rfl fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ hF => by
        rw [rAddr_x10_x0 hx]; exact (hbuf σ0 c0 hJp 0 (.inl rfl)).2.1 m hF
    exact nodeW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L19_wc_rodata.sp0") (k := 2) rfl hS.l1 (by free_decH)
      (by decide) (by decide +kernel) h.1 (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inl h))) hpl.l1 h.2
  · exact blkW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (rl := ".L19_wc_rodata.sp0") (k := 3) (ra := none) b1
      rfl rpB1_ok hR hal hRlo hhi hS.s1 (by decide) (fun _ h => by cases h) (by decide +kernel)
      (nr (by decide)) (by free_decH) (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inl h)))) hpl.s1
  · exact nodeW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L19_wc_rodata.sp0") (k := 9) rfl hS.x1 (by free_decH)
      (by decide) (by decide +kernel)
      (Spike.Lib.A64.WakeWf.st_step hI (by rw [hp]; exact bx1) rfl fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by
        rw [rAddr_x10_x0 hx]; exact (hbuf σ0 c0 hJp 0 (.inl rfl)).2.1 m hF)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inl h)))) hpl.x1 hwr1
  · exact blkW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (rl := ".L19_wc_rodata.sp0") (k := 10) (ra := none) b2
      rfl rpB2_ok hR hal hRlo hhi hS.s2 (by decide) (fun _ h => by cases h) (by decide +kernel)
      (nr (by decide)) (by free_decH) (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inl h))))) hpl.s2
  · have h := ld_stepH (ar := ar) (p := p) (lbl := lbl) (lsize := lsize) (Ctx := Ctx) (R := R) hp
      (n := pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .l2) (k := 11) bl2 rfl fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ hF => by
        rw [rAddr_x10_x0 hx]; exact (hbuf σ0 c0 hJp 8 (.inr rfl)).2.1 m hF
    exact nodeW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L19_wc_rodata.sp0") (k := 11) rfl hS.l2
      (by free_decH) (by decide) (by decide +kernel) h.1
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inl h)))))) hpl.l2 h.2
  · exact blkW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (rl := ".L19_wc_rodata.sp0") (k := 12) (ra := none) b3
      rfl rpB3_ok hR hal hRlo hhi hS.s3 (by decide) (fun _ h => by cases h) (by decide +kernel)
      (nr (by decide)) (by free_decH)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h))))))) hpl.s3
  · exact nodeW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L19_wc_rodata.sp0") (k := 17) rfl hS.x2
      (by free_decH) (by decide) (by decide +kernel)
      (Spike.Lib.A64.WakeWf.st_step hI (by rw [hp]; exact bx2) rfl fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by
        rw [rAddr_x10_x0 hx]; exact (hbuf σ0 c0 hJp 8 (.inr rfl)).2.1 m hF)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h))))))) hpl.x2 hwr2
  · have key : ∀ s c, At L.exe L.endPc R F (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .f) s c →
        ∃ hc : Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .DMB .st⟩) 4,
          isaLSE2.exec s = some (.fence .st fun _ => .done (Kraken.Promising.Lower.A64.after s 4 s.st.1)) := by
      rintro s c ⟨h1, h2, -, h4', -⟩
      have hc := cell1H hp bf h1 h2 h4'
      exact ⟨hc, Kraken.Promising.Lower.A64.exec_dmb hc⟩
    refine nodeW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (l := ".L19_wc_rodata.sp0") (k := 18) rfl hS.f
      (by free_decH) (by decide) (by decide +kernel) (fun s c hA => ?_)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))) hpl.f
      (Spike.Lib.A64.WakeWf.nodeW_noWrC fun s c hA => ⟨fun Lc hW => ?_, fun _ h => h⟩)
    · obtain ⟨hc, hx⟩ := key s c hA
      refine ⟨.instr ⟨.W64, .DMB .st⟩, _, hc, fun imm h => by simp at h, hx, fun s' hu => ?_⟩
      obtain ⟨_, hu⟩ := hu
      simp only [Scc.Sem.TreeLeaf] at hu
      subst hu; rfl
    · obtain ⟨_, hx⟩ := key s c hA
      rcases hW with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hx] at h <;> cases h
  · have hend : ∀ σ c, (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .s4).J σ c →
        (Spike.Lib.A64.Flow.arun L.lab rpB4
          ⟨L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19), ⟨-48, []⟩, σ⟩).pc = L.lab ".L1_scc_rt_main.sp0" := by
      rintro σ c ⟨σ0, ⟨c0, hJp⟩, -, -, -, h8⟩
      rw [rpB4_run, h8, hra σ0 c0 hJp, Int64.ofBitVec_toBitVec]
    exact blkW_rpWSHA hp hlo hΛ hlab hsite hcl hX0 (rl := ".L1_scc_rt_main.sp0") (k := 19)
      (ra := some ".L1_scc_rt_main.sp0") b4 rfl rpB4_ok hR hal hRlo hhi hS.s4 (by decide) (fun _ h => by cases h; rfl)
      (by decide +kernel) (Spike.Lib.A64Consumer.hret_of_run rpB4_ok hend) (by free_decH)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))) hpl.s4

/-- **`scc_rt_main`'s `.sp0` block inside `WSH`** (the call of `wc_main`), in
`scc_rt_main`'s region `R`: its controls' facts (`hcf`, at `wc_rodata`'s
return invariant `Jr`), its frames placed (`hpl`). -/
theorem mB1W_WSH (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {σC : Spike.Lib.A64.Flow.AS} {Jr : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hcf : ∀ σ c, Jr σ c → (∀ a, c.term ≠ .ret a) ∧ RunWf p c [])
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F (mS0 L.lab R σC Jr) mB1) :
    BlkW (WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc R F
      (mS0 L.lab R σC Jr) mB1 := by
  have hin := Spike.Lib.A64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.A64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, b1⟩, -⟩, -⟩ := hin
  exact blkW_rpWSH hp hlo hΛ hlab hsite hcl hX0 (rl := ".L1_scc_rt_main.sp0") (k := 0) (ra := none) b1
    (ofNat4_zero _) mB1_ok hR hal hRlo hhi
    (Spike.Lib.A64.HelloPh.WcW.mB1W_wcGH hp hlo hΛ hlab hsite a hR hal hRlo hhi) (by decide)
    (fun _ h => by cases h) (by decide +kernel)
    (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim) (by free_decH)
    (fun _ c ⟨σx, h, _⟩ => hcf σx c h) hpl

end Gen

end Spike.Lib.A64.HelloPh.RdWfS

/-! ## Axioms -/

/-- info: 'Spike.Lib.A64.HelloPh.RdWfS.blkW_rpWSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfS.blkW_rpWSH

/-- info: 'Spike.Lib.A64.HelloPh.RdWfS.rdPostW_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfS.rdPostW_WSH

/-- info: 'Spike.Lib.A64.HelloPh.RdWfS.mB1W_WSH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdWfS.mB1W_WSH
