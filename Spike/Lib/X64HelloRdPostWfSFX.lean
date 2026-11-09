/-
**hello.w's `wc_rodata` from the allocator's return, and `scc_rt_main`'s `.x2` block, inside the start's level
at `ownGHXW`** (x86-64; the twin of `Spike/Lib/A64HelloRdPostWfSF.lean`, at `ownGHXW`): `HelloRd.RdPostW` and
`mB1` at `AllocWSF.WSHFg (ownGHXW L a) … fs` (`fs` one of `[]` and `[frM]`, `hfs`), moved only by the take.
rodata's states are at `[HelloRdCf.frH env]`, the `.x2` block's (after rodata's `ret` pops the frame) at `[]`.
Each node's `SFactsSt2` at `ownGHXW` is `OwnRd.rdPostW_wcGHX`'s / `mB1W_wcGHX`'s; the controls' facts (`hcf`), the
frames placed (`hpl`) and the writes' obligations (`hwr1`, `hwr2`) are at `fs`.

- `blkW_rpWSHFg`, `nodeW_rpWSHFg`: a block (its `ret`s to `L.lab rl`), a single instruction of `rpTabH` inside
  `WSHFg own` at any `own`.
- `rdPostW_WSHX`: `RdPostW` inside `WSHFg (ownGHXW L a) … fs`.
- `mB1W_WSHX`: the `.x2` block of `scc_rt_main` inside `WSHFg (ownGHXW L a) … fs`.

## Differences from the AArch64 version

- AArch64's level is at `ownGH` (main owns no TCB word there); here it is `WSHFg (ownGHXW L a)`, and the producers
take `ownGHXW`'s separation premises (`hsep`, `ha`, `hW`), the frames' bands
on the pool (`hb : BandOnP L R (-208) 8` for `wc_rodata`, as `RdWfSFX.rdPreW_WSHX`'s; `hbM : BandOnP L R (-288) 8`
for `scc_rt_main`'s `.x2`), and the buffer's two words off `tcbM` (`hbufM`). The load's step and no-write
(`RdWfSF.ld_stepHF`) are own-free, in `X64HelloRdPostWfSF`.
- There is no publish fence (scc's `# fence st` emits no code under TSO): `RdPostW` has no `J5` and no fence
  node, so `rdPostW_WSHX` has nine cases (AArch64: ten, the `dmb st` at `.sp0 + 18` words).
- Offsets are bytes and cells sized: `.x15`'s nodes at 0, 8, 11, 29, 32, 36, 40, 58, 62; a block's free pcs are
  `freeBlkH l k blk`, a node's `freeAtH l [k]`, its fact `PhFact.step l k z`; the phase checks are
  `HelloWf.phOffW` / `siOffW` (AArch64's `phOffHC` / `siOffHC`); a block's fact carries its return label with an
  offset (`ra : Option (String × Nat)`).
- The loads and stores are `movq k(%rcx), %rax` / `movq %rax, k(%rcx)` at the buffer `%rax` of `.x15`'s entry
  (`bAddr_rcx_rax`; AArch64's `ldr`/`str x9, [x10, #i]` at `x0`).
- `ret` reads the return address at the stack top, so `hra` is about `σ0.slot 0` and the return label is
  `.Lscc_rt_main.x0` (AArch64: the saved `x30` at `-8`, `.L1_scc_rt_main.sp0`).
- No 16-alignment; the bounds are x86-64's: `R.lo ≤ -40`, `8 ≤ R.hi` for `wc_rodata`, `R.lo ≤ -288`,
  `8 ≤ R.hi` for `.x2`.
-/
import Spike.Lib.X64HelloRdPostWfSF
import Spike.Lib.X64HelloRdPostWIX
import Spike.Lib.X64HelloRdWfSFX

namespace Spike.Lib.X64.HelloPh.RdWfSFX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (PhFact blockAtB okPcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At cellOff okBlk arun bAddr)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.WakeWf (RunWf NoWrC)
open Spike.Lib.X64.HelloPh (lo ownGHXW instOkH)
open Spike.Lib.X64.HelloPh.WcW (freeNH freeAtH freeBlkH freeAt_pcH freeBlk_pcH rpTabH rpW_factH BoxOkH)
open Spike.Lib.X64.HelloWf (WSHFg)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.Flow.HelloRd (pN RdPostW rpIn hello_rpIn)
open Spike.Lib.X64.Flow.Hello1 (rpB0 rpB0_ok rpB1 rpB1_ok rpB2 rpB2_ok rpB3 rpB3_ok rpB4 rpB4_ok rpB4_run
  bAddr_rcx_rax mB1 mB1_ok mS0)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Arena FragS)
open Kraken.Promising.Lower.X64 (CellAt)

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {own : Spike.Lib.X64Consumer.Own} {rS : Range} {R : Spike.Lib.Region}
  {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {K : State → State → Prop} {fs : List TermRun.Frame}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s) (hfs : fs = [] ∨ fs = [frM])

include hp hlo hΛ hlab hsite hcl hX0 hfs

/-! ## A block and a node inside `WSHFg own` -/

/-- **A covered block of `rpTabH` inside `WSHFg own`** (AArch64 `RdWfSF.blkW_rpWSHF` at any `own`), its `ret`s to
`L.lab rl` (`hret`; `rl` the fact's return label, `hra`): its `SFactsSt2` at `own` (`hst`), its abort phases'
check (`hph`), its pcs free (`hfree`), its controls' facts (`hJ`), its frames placed (`hpl`). -/
theorem blkW_rpWSHFg {n : ND} {blk : List (Directive × Nat)} {l rl : Label} {k : Nat} {blo bhi : Int}
    {ra : Option (String × Nat)}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH)
    (hra : ∀ r o', ra = some (r, o') → L.lab rl = L.lab r + Int64.ofNat o')
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hfree : freeBlkH l k blk = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := L.lab rl) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (rpW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  have hI := instOkH hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  refine Spike.Lib.X64.WakeWf.blkW_w0 hfs ?_
    (Spike.Lib.X64.HelloPh.StartWf.blkW_wfQH (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
      (fs := fs) hI (hp ▸ hb) he hok hR hlo' hhi hst'
      (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
      (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl hJ hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  show freeNH (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true
  rw [← he]; exact freeBlk_pcH hlab hfree hj

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcrossB`): as `blkW_rpWSHFg`. -/
theorem blkW_rpWSHFgA {n : ND} {blk : List (Directive × Nat)} {l rl m : Label} {k jA : Nat} {blo bhi : Int}
    {ra : Option (String × Nat)}
    (hb : Scc.Cert.Rt.X64.blockAcrossB helloCells l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hst : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n blk)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH)
    (hra : ∀ r o', ra = some (r, o') → L.lab rl = L.lab r + Int64.ofNat o')
    (hph : Spike.Lib.X64.HelloWf.phOffW pfxM l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = L.lab rl)
    (hfree : freeBlkH l k blk = true)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n blk) :
    BlkW (WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n blk := by
  have hph' := Spike.Lib.X64.Rt.PhOfTab.blkPh_of_factOk hlab (rapc := L.lab rl) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (rpW_factH hΛ hf)
  have hokpc : ∀ j < blk.length,
      okPcOf lo helloCells L.Λ (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true := fun j hj => by
    have := List.all_eq_true.mp hph' j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true] at this
    rw [← he]; exact this.1.1
  have hI := instOkH hp hlo 0#64 (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hst' : BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s Dt) K L.exe L.endPc R F n blk :=
    fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
      let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
      ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩
  refine Spike.Lib.X64.WakeWf.blkW_w0 hfs ?_
    (Spike.Lib.X64.HelloPh.StartWf.blkW_wfQHA (Λ := L.Λ) (ar := ar) (p := p) (Ctx := Ctx) (lsize := lsize)
      (fs := fs) hI (hp ▸ hb) he hok hR hlo' hhi hst'
      (fun j hj s h1 h2 h3 => (hI.off s (by unfold pcOf; rw [h3]; exact hokpc j hj)).1)
      (Spike.Lib.X64.HelloWf.phOffW_sound hlab hph) hret hcl hJ hpl)
  intro s σ c _ _ _ _ _ _ _ j hj m _ _
  refine ⟨hX0 _ ?_, fun _ h => h⟩
  show freeNH (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat = true
  rw [← he]; exact freeBlk_pcH hlab hfree hj

/-- **A single instruction of `rpTabH` without an event inside `WSHFg own`** (AArch64 `RdWfSF.nodeW_rpWSHF` at
any `own`). -/
theorem nodeW_rpWSHFg {n : ND} {l : Label} {k z : Nat} (he : L.lab l + Int64.ofNat k = n.pc)
    (hst : NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) own s) K L.exe L.endPc R F n)
    (hfree : freeAtH l [k] = true) (hf : PhFact.step l k z ∈ rpTabH)
    (hph : Spike.Lib.X64.HelloWf.siOffW pfxM l k z = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s' : State, TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : NodeW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F n)
    (hwr : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F n) :
    NodeW (WSHFg own L ar p Dt Cl Ctx lbl lsize frM X0 fs) K L.exe L.endPc R F n := by
  have hf0 : freeNH n.pc.toBitVec.toNat = true := by
    rw [← he]; exact freeAt_pcH hlab hfree (List.mem_singleton.mpr rfl)
  have hok := (Spike.Lib.X64.Rt.PhOfTab.step_of_factOk hlab (rpW_factH hΛ hf)).1
  rw [he] at hok
  refine Spike.Lib.X64.WakeWf.nodeW_w0 hfs ?_
    (Spike.Lib.X64.HelloPh.WcWfX.nodeW_wfCX (Dt := Dt) (Cl := Cl) hp hlo hlab he hst
      (Spike.Lib.X64.HelloPh.WcWf.htk_of_freeNH hlab hsite hf0) hok hph hstep hcl hJ hpl hwr)
  rintro s c ⟨_, _, _, hpc, _⟩
  exact ⟨hX0 _ (by unfold pcOf; rw [hpc]; exact hf0), fun _ h => h⟩

/-! ## `wc_rodata` from the allocator's return -/

set_option maxHeartbeats 1600000 in
/-- **`RdPostW` inside `WSHFg (ownGHXW L a)`**, moved only by the take: AArch64 `RdWfSF.rdPostW_WSHF`'s premises,
`ownGHXW`'s separation (`hsep`, `ha`, `hW`), `wc_rodata`'s band `[-208, 8]` on the pool (`hb`), and the buffer's two
words off `tcbM` (`hbufM`). -/
theorem rdPostW_WSHX
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-208) 8)
    (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 : Spike.Lib.X64.AS → Ctl → Prop}
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) → BoxOkH L.Λ L a F (bAddr σ0.regs .rax i))
    (hbufM : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) → bAddr σ0.regs .rax i ≠ tcbM L)
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot 0 = (L.lab ".Lscc_rt_main.x0").toBitVec)
    (hcf : ∀ σ0 c, (Jp σ0 c ∨ Jp' σ0 c ∨ J1 σ0 c ∨ J2 σ0 c ∨ J2' σ0 c ∨ J3 σ0 c ∨ J4 σ0 c) →
      (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : RdPostW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F
      Jp Jp' J1 J2 J2' J3 J4)
    (hwr1 : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .x1))
    (hwr2 : NodeW (NoWrC ar p lbl lsize Ctx fs) (fun _ _ => False) L.exe L.endPc R F
      (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .x2)) :
    RdPostW (WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc
      R F Jp Jp' J1 J2 J2' J3 J4 := by
  have hS := Spike.Lib.X64.HelloPh.OwnRd.rdPostW_wcGHX (Λ := L.Λ) (rS := rS) (Jp' := Jp') (J1 := J1) (J2 := J2)
    (J2' := J2') (J3 := J3) (J4 := J4) hp hlo hΛ hlab hsite hsep ha hW hb hR hRlo hhi hbuf hbufM hra
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b0, bl1⟩, b1⟩, bx1⟩, b2⟩, bl2⟩, b3⟩, bx2⟩, b4⟩ := hin
  have nr : ∀ {blk : List (Directive × Nat)}, Spike.Lib.X64Consumer.noRetBlk blk = true → ∀ {n : ND} {x : Int64},
      ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp) = x :=
    fun hnr _ _ _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hnr j hj hr).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (rl := ".Lwc_rodata.x0") (k := 0) (ra := none)
      b0 (ofNat_zero' _) rpB0_ok hR hRlo hhi hS.s0 (by decide) (fun _ _ h => by cases h)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (nr (by decide)) (by wcfreeBH_dec)
      (fun σ c h => hcf σ c (.inl h)) hpl.s0
  · have h := Spike.Lib.X64.HelloPh.RdWfSF.ld_stepHF (ar := ar) (p := p) (lbl := lbl) (lsize := lsize)
      (Ctx := Ctx) (R := R) (fs := fs) hp hlo hsite (n := pN L.lab Jp Jp' J1 J2 J2' J3 J4 .l1) (k := 8) bl1 rfl
      fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ hF => by
        rw [bAddr_rcx_rax hx]; exact (hbuf σ0 c0 hJp 0 (.inl rfl)).2.1 m hF
    exact nodeW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.x0") (k := 8) rfl hS.l1
      (by wcfreeH_dec) (by decide) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) h.1
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inl h))) hpl.l1 h.2
  · exact blkW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (rl := ".Lwc_rodata.x0") (k := 11) (ra := none)
      b1 rfl rpB1_ok hR hRlo hhi hS.s1 (by decide) (fun _ _ h => by cases h)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (nr (by decide)) (by wcfreeBH_dec)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inl h)))) hpl.s1
  · exact nodeW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.x0") (k := 29) (z := 3) rfl hS.x1
      (by wcfreeH_dec) (by decide) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel)
      (Spike.Lib.X64.WakeWf.st_step hI (by rw [hp]; exact bx1) rfl
        fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by
          rw [bAddr_rcx_rax hx]; exact (hbuf σ0 c0 hJp 0 (.inl rfl)).2.1 m hF)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inl h)))) hpl.x1 hwr1
  · exact blkW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (rl := ".Lwc_rodata.x0") (k := 32) (ra := none)
      b2 rfl rpB2_ok hR hRlo hhi hS.s2 (by decide) (fun _ _ h => by cases h)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (nr (by decide)) (by wcfreeBH_dec)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inl h))))) hpl.s2
  · have h := Spike.Lib.X64.HelloPh.RdWfSF.ld_stepHF (ar := ar) (p := p) (lbl := lbl) (lsize := lsize)
      (Ctx := Ctx) (R := R) (fs := fs) hp hlo hsite (n := pN L.lab Jp Jp' J1 J2 J2' J3 J4 .l2) (k := 36) bl2 rfl
      fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ hF => by
        rw [bAddr_rcx_rax hx]; exact (hbuf σ0 c0 hJp 8 (.inr rfl)).2.1 m hF
    exact nodeW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.x0") (k := 36) rfl hS.l2
      (by wcfreeH_dec) (by decide) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel) h.1
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inl h)))))) hpl.l2 h.2
  · exact blkW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (rl := ".Lwc_rodata.x0") (k := 40) (ra := none)
      b3 rfl rpB3_ok hR hRlo hhi hS.s3 (by decide) (fun _ _ h => by cases h)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (nr (by decide)) (by wcfreeBH_dec)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h))))))) hpl.s3
  · exact nodeW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (l := ".Lwc_rodata.x0") (k := 58) (z := 4) rfl hS.x2
      (by wcfreeH_dec) (by decide) (by unfold Spike.Lib.X64.HelloWf.siOffW; decide +kernel)
      (Spike.Lib.X64.WakeWf.st_step hI (by rw [hp]; exact bx2) rfl
        fun σ c m ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ hF => by
          rw [bAddr_rcx_rax hx]; exact (hbuf σ0 c0 hJp 8 (.inr rfl)).2.1 m hF)
      (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h))))))) hpl.x2 hwr2
  · have hend : ∀ σ c, (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .s4).J σ c →
        (arun L.lab rpB4 ⟨L.lab ".Lwc_rodata.x0" + 62, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc =
          L.lab ".Lscc_rt_main.x0" := by
      rintro σ c ⟨σ0, ⟨c0, hJp⟩, -, hfr⟩
      rw [rpB4_run, hfr.2.2.1, hra σ0 c0 hJp, Int64.ofBitVec_toBitVec]
    exact blkW_rpWSHFgA hp hlo hΛ hlab hsite hcl hX0 hfs (rl := ".Lscc_rt_main.x0") (k := 62)
      (ra := some (".Lscc_rt_main.x0", 0)) b4 rfl rpB4_ok hR hRlo hhi hS.s4 (by decide)
      (fun _ _ h => by cases h; exact (ofNat_zero' _).symm)
      (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel) (Spike.Lib.X64Consumer.hret_of_run rpB4_ok hend)
      (by wcfreeBH_dec) (fun _ c ⟨σ0, _, h, _⟩ => hcf σ0 c (.inr (.inr (.inr (.inr (.inr (.inr h))))))) hpl.s4

/-- **`scc_rt_main`'s `.x2` block inside `WSHFg (ownGHXW L a)`** (AArch64 `RdWfSF.mB1W_WSHF` at `ownGHXW`), in
`scc_rt_main`'s region `R`, its band `[-288, 8]` on the pool (`hbM`): its controls' facts (`hcf`, at
`wc_rodata`'s return invariant `Jr`), its frames placed (`hpl`). -/
theorem mB1W_WSHX
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hbM : BandOnP L R (-288) 8)
    (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {σC : Spike.Lib.X64.AS} {Jr : Spike.Lib.X64.AS → Ctl → Prop}
    (hcf : ∀ σ c, Jr σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ RunWf p c fs)
    (hpl : BlkW (fun s c => PlacedSE L.Λ lbl s c fs) (fun _ _ => False) L.exe L.endPc R F (mS0 L.lab R σC Jr) mB1) :
    BlkW (WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 fs) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F
      (mS0 L.lab R σC Jr) mB1 := by
  have hin := Spike.Lib.X64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.X64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, b1⟩, -⟩, -⟩ := hin
  exact blkW_rpWSHFg hp hlo hΛ hlab hsite hcl hX0 hfs (rl := ".Lscc_rt_main.x0") (k := 0) (ra := none) b1
    (ofNat_zero' _) mB1_ok hR hRlo hhi
    (Spike.Lib.X64.HelloPh.OwnRd.mB1W_wcGHX hp hlo hΛ hlab hsite hsep ha hW hbM hR hRlo hhi) (by decide)
    (fun _ _ h => by cases h) (by unfold Spike.Lib.X64.HelloWf.phOffW; decide +kernel)
    (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim) (by wcfreeBH_dec)
    (fun _ c ⟨σx, h, _⟩ => hcf σx c h) hpl

end Gen

end Spike.Lib.X64.HelloPh.RdWfSFX

/-! ## Axioms -/

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.blkW_rpWSHFg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.blkW_rpWSHFg

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.nodeW_rpWSHFg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.nodeW_rpWSHFg

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.rdPostW_WSHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.rdPostW_WSHX

/--
info: 'Spike.Lib.X64.HelloPh.RdWfSFX.mB1W_WSHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdWfSFX.mB1W_WSHX
