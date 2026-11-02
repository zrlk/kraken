/-
**hello.w's `wc_rodata` from the allocator's return, and `scc_rt_main`'s
`.x2` block, inside `SFactsSt2` at `ownGH`** (x86-64; twin of
`Spike/Lib/A64HelloRdPostWI.lean`): the `SFactsSt2` component of
`HelloRd.RdPostW` (`.x15`'s blocks, the two exchanges' loads and stores at
the buffer, the return to `scc_rt_main`'s `.x2`) and of `scc_rt_main`'s `.x2`
block (`Hello1.mB1`, up to `call wc_main`). Each node is
`Rt.blkW_pre`/`Rt.nodeW_*_pre` at `instOkH`, moved to `ownGH` at its free pcs;
the phase facts are decided by the kernel against helloCells' labels
(`rpTabH`).

- `rpTabH`, `rpFactsH`, `rpW_factH`: the blocks' phase facts.
- `blkW_rpGH`: a covered block of `rpTabH`, its `ret`s to `rapc` (`hret`).
- `mapped_rd`: a word mapped for writing is mapped for reading.
- `ldW_rpGH`, `stW_rpGH`: a load or store `k(%rcx)` at `.x15 + o` of a buffer
  word `BoxOkH`.
- `rdPostW_wcGH`: `RdPostW` at `SFactsSt2`/`ownGH`, the buffer's two words
  `BoxOkH` at `.x15` (`hbuf`), the saved return address `scc_rt_main`'s `.x2`
  (`hra`).
- `mB1W_wcGH`: `scc_rt_main`'s `.x2` block at `SFactsSt2`/`ownGH`.

## Differences from the AArch64 version

- There is no publish fence: scc's `# fence st` emits no code under TSO
  (`HelloRd.pN` has no fence node), so AArch64's `fenW_rpGH` has no twin.
- Offsets are bytes: the free pcs are `freeAtH ".Lwc_rodata.x15" os` at
  `.x15`'s node offsets (AArch64's `freeSp0H` over `4 k`, `k < 20`), and the
  loads and stores are the generic `ldW_rpGH`/`stW_rpGH` at an offset `o` and
  size `z` (`movq k(%rcx), %rax` / `movq %rax, k(%rcx)`; AArch64's
  `ldr`/`str x9, [x10, #i]`).
- The block after the allocator's return is `.Lwc_rodata.x15` (AArch64's
  `.L19_wc_rodata.sp0`) and the return label `.Lscc_rt_main.x2` (AArch64's
  `.L1_scc_rt_main.sp0`); `ret` reads the return address at the stack top, so
  `hra` is about `σ0.slot 0` (AArch64's saved `x30` at `-8`).
- No 16-alignment; the bounds are x86-64's: `R.lo ≤ -40`, `8 ≤ R.hi` for
  `wc_rodata` (`rpB*_ok`) and `R.lo ≤ -288`, `8 ≤ R.hi` for `.x2`
  (`Hello1.mB1_ok`).
-/
import Spike.Lib.X64HelloRdPreWI
import Spike.Lib.X64HelloMain

namespace Spike.Lib.X64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk blockAtB code_field)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At arun okBlk bAddr mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add')
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)
open Kraken.Promising.Lower.X64 (eaddr exec_load_agrees exec_store_agrees)
open Spike.Lib.X64.HelloPh
open Spike.Lib.X64.WakePh.WcW (blkW_mapC c0N_cfacts NodeW.ofAll)
open Spike.Lib.X64.Flow.HelloRd (pN RdPostW rpIn hello_rpIn)
open Spike.Lib.X64.Flow.Hello1 (rpB0 rpB0_ok rpB0_run rpB1 rpB1_ok rpB1_run rpB2 rpB2_ok rpB2_run rpB3
  rpB3_ok rpB3_run rpB4 rpB4_ok rpB4_run bAddr_rcx_rax mB1 mB1_ok mB1_run mS0)

/-! ## The blocks' phase facts -/

/-- **`.x15`'s blocks and single instructions, and `scc_rt_main`'s `.x2`
block**: the last block of `wc_rodata` returns to `scc_rt_main`'s `.x2`. -/
def rpTabH : List PhFact :=
  [.blk ".Lwc_rodata.x15" 0 rpB0 none none,
   .step ".Lwc_rodata.x15" 8 3,
   .blk ".Lwc_rodata.x15" 11 rpB1 none none,
   .step ".Lwc_rodata.x15" 29 3,
   .blk ".Lwc_rodata.x15" 32 rpB2 none none,
   .step ".Lwc_rodata.x15" 36 4,
   .blk ".Lwc_rodata.x15" 40 rpB3 none none,
   .step ".Lwc_rodata.x15" 58 4,
   .blk ".Lwc_rodata.x15" 62 rpB4 (some (".Lscc_rt_main.x2", 0)) none,
   .blk ".Lscc_rt_main.x2" 0 mB1 none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem rpFactsH : rpTabH.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

/-- **A fact of `rpTabH` at `phH`.** -/
theorem rpW_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ rpTabH) : factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH f = true := by
  have := List.all_eq_true.mp rpFactsH f hf
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at this
  exact this

/-- A word mapped for writing is mapped for reading. -/
theorem mapped_rd {x : Scc.Sem.Kernel.KState} {l : Loc} (h : Scc.Sem.Kernel.mapped x true l = true) :
    Scc.Sem.Kernel.mapped x false l = true := by
  unfold Scc.Sem.Kernel.mapped at *
  simp only [List.all_eq_true, List.any_eq_true] at *
  intro i hi
  obtain ⟨r, hr, h⟩ := h i hi
  refine ⟨r, ?_, h⟩
  simp only [Scc.Sem.Kernel.mappedRegions, ite_true, List.append_nil, List.mem_append] at hr
  simp only [Scc.Sem.Kernel.mappedRegions, Bool.false_eq_true, ite_false, List.mem_append]
  exact .inl hr

variable {L : RuntimeLayout} {Λ : Scc.Sem.Layout} {rS : Range} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A covered block of `rpTabH` inside `SFactsSt2` at `ownGH`** (`blkW_rdGH`
with its `ret`s to `rapc`, `hret`): `blkW_pre` at `instOkH`, the control
replaced by `c0`, moved to `ownGH` at its free pcs (`hfree`) and free end
(`hlast`). -/
theorem blkW_rpGH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    {ra : Option (String × Nat)} {rapc : Int64}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH) (hra : ∀ r o', ra = some (r, o') → rapc = L.lab r + Int64.ofNat o')
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp)
        = rapc)
    (hfree : freeBlkH l k blk = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.X64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := rapc) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) (rpW_factH hΛ hf)
  have hW := Spike.Lib.X64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun σ _ hJ => let ⟨c', hJ'⟩ := hJ.2; hret σ c' hJ') (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := code_field L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeBlk_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.X64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- `.x15`'s node pcs and its return label `.x2` are free. -/
theorem freeX15H : freeAtH ".Lwc_rodata.x15" [0, 8, 11, 29, 32, 36, 40, 58, 62] = true := by
  wcfreeH_dec

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **A load `movq k(%rcx), %rax` at `.x15 + o` of a word `BoxOkH`** inside
`SFactsSt2` at `ownGH`: `BoxOkH` at its address at every state (`hbox`), its
pc and next pc free (`hfr`). -/
theorem ldW_rpGH (a : BitVec 64) {n : ND} {k : Int64} {o z : Nat}
    (hb : blockAtB helloCells ".Lwc_rodata.x15" o [(Spike.Lib.X64.ldDir .rcx k .rax, z)] = true)
    (he : n.pc = L.lab ".Lwc_rodata.x15" + Int64.ofNat o)
    (hf : PhFact.step ".Lwc_rodata.x15" o z ∈ rpTabH) (hfr : freeAtH ".Lwc_rodata.x15" [o, o + z] = true)
    (hbox : ∀ σ c, n.J σ c → BoxOkH Λ L a F (bAddr σ.regs .rcx k)) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hb' : blockAtB L.prog ".Lwc_rodata.x15" o [(Spike.Lib.X64.ldDir .rcx k .rax, z)] = true := by
    rw [hp]; exact hb
  have hs := step_of_factOk hlab (rpW_factH hΛ hf)
  have f0 := freeAt_pcH hlab hfr (o := o) (by simp)
  have fz := freeAt_pcH hlab hfr (o := o + z) (by simp)
  rw [ofNat_add'] at fz
  refine NodeW.ofAll (fun σ => bAddr σ.regs .rcx k) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    exact absurd (hbox σ c hJ) hA
  obtain ⟨hmw, hun, -⟩ := hA
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.X64.Rt.nodeW_ld_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) hb' rfl he c0N_cfacts hs.1
      (fun _ _ h => h) hs.2 ?_ (mapped_rd hmw) hun) (by rw [he]; exact f0) (by rw [he]; exact fz) ?_
  · rintro σ c ⟨-, c', -, rfl⟩
    rfl
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, hJ, hsA⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb' rfl h1 h2 (h4'.trans he)
    have ha' : eaddr s z (mB .rcx k) = A := (eaddr_mB s z .rcx k).trans (by rw [hAb.regs]; exact hsA)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_load_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    obtain ⟨_, hu⟩ := hu
    simp only [TreeLeaf] at hu
    subst hu; rfl

/-- **A store `movq %rax, k(%rcx)` at `.x15 + o` of a word `BoxOkH`** inside
`SFactsSt2` at `ownGH` (as `ldW_rpGH`). -/
theorem stW_rpGH (a : BitVec 64) {n : ND} {k : Int64} {o z : Nat}
    (hb : blockAtB helloCells ".Lwc_rodata.x15" o [(Spike.Lib.X64.stDir .rcx k .rax, z)] = true)
    (he : n.pc = L.lab ".Lwc_rodata.x15" + Int64.ofNat o)
    (hf : PhFact.step ".Lwc_rodata.x15" o z ∈ rpTabH) (hfr : freeAtH ".Lwc_rodata.x15" [o, o + z] = true)
    (hbox : ∀ σ c, n.J σ c → BoxOkH Λ L a F (bAddr σ.regs .rcx k)) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := rS)
  have hb' : blockAtB L.prog ".Lwc_rodata.x15" o [(Spike.Lib.X64.stDir .rcx k .rax, z)] = true := by
    rw [hp]; exact hb
  have hs := step_of_factOk hlab (rpW_factH hΛ hf)
  have f0 := freeAt_pcH hlab hfr (o := o) (by simp)
  have fz := freeAt_pcH hlab hfr (o := o + z) (by simp)
  rw [ofNat_add'] at fz
  refine NodeW.ofAll (fun σ => bAddr σ.regs .rcx k) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    exact absurd (hbox σ c hJ) hA
  obtain ⟨hmw, hun, hno⟩ := hA
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.X64.Rt.nodeW_st_pre hI (Λ := Λ) (rS := rS) (lbl := fun _ => none) (ownOf := ownH L a)
      (fun _ => rfl) hb' rfl he c0N_cfacts hs.1 (fun _ _ h => h) hs.2 ?_ hmw hun hno)
    (by rw [he]; exact f0) (by rw [he]; exact fz) ?_
  · rintro σ c ⟨-, c', -, rfl⟩
    rfl
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, hJ, hsA⟩
    have hc := Spike.Lib.X64.Rt.cellOf hI hb' rfl h1 h2 (h4'.trans he)
    have ha' : eaddr s z (mB .rcx k) = A := (eaddr_mB s z .rcx k).trans (by rw [hAb.regs]; exact hsA)
    refine ⟨_, _, hc, fun w w' h => (by cases h), exec_store_agrees hc ha' (hun _ hF) (agrees_of_decls h3' _ _),
      fun s' hu => ?_⟩
    simp only [TreeLeaf] at hu
    obtain ⟨_, rfl⟩ := hu; rfl

/-- **`RdPostW` inside `SFactsSt2` at `ownGH`** (owned word `a`), none moved by
the take: the buffer's two words `BoxOkH` at every `.x15` state (`hbuf`), the
return address at the stack top `scc_rt_main`'s `.x2` (`hra`). -/
theorem rdPostW_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) → BoxOkH Λ L a F (bAddr σ0.regs .rax i))
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot 0 = (L.lab ".Lscc_rt_main.x2").toBitVec) :
    RdPostW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b0, bl1⟩, b1⟩, bx1⟩, b2⟩, bl2⟩, b3⟩, bx2⟩, b4⟩ := hin
  have fx : ∀ o, o ∈ [0, 8, 11, 29, 32, 36, 40, 58, 62] →
      freeNH (L.lab ".Lwc_rodata.x15" + Int64.ofNat o).toBitVec.toNat = true :=
    fun o ho => freeAt_pcH hlab freeX15H ho
  have nr : ∀ {blk : List (Directive × Nat)}, Spike.Lib.X64Consumer.noRetBlk blk = true → ∀ {n : ND},
      ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), Spike.Lib.X64.classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp) = 0 :=
    fun hnr _ _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hnr j hj hr).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 0) (ra := none) (rapc := 0) b0 (ofNat_zero' _) rpB0_ok hR
      hRlo hhi (by decide) (fun _ _ h => by cases h) (nr (by decide)) (by wcfreeBH_dec) fun σ c _ => ?_
    show freeNH (arun L.lab rpB0 ⟨L.lab ".Lwc_rodata.x15", Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat = true
    rw [rpB0_run]; exact fx 8 (by simp)
  · exact ldW_rpGH hp hlo hΛ hlab hsite a (o := 8) bl1 rfl (by decide) (by wcfreeH_dec)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hbuf σ0 c0 hJp 0 (.inl rfl)
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 11) (ra := none) (rapc := 0) b1 rfl rpB1_ok hR hRlo hhi
      (by decide) (fun _ _ h => by cases h) (nr (by decide)) (by wcfreeBH_dec) fun σ c _ => ?_
    show freeNH (arun L.lab rpB1 ⟨L.lab ".Lwc_rodata.x15" + 11, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat
      = true
    rw [rpB1_run, Int64.add_assoc]; exact fx 29 (by simp)
  · exact stW_rpGH hp hlo hΛ hlab hsite a (o := 29) bx1 rfl (by decide) (by wcfreeH_dec)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hbuf σ0 c0 hJp 0 (.inl rfl)
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 32) (ra := none) (rapc := 0) b2 rfl rpB2_ok hR hRlo hhi
      (by decide) (fun _ _ h => by cases h) (nr (by decide)) (by wcfreeBH_dec) fun σ c _ => ?_
    show freeNH (arun L.lab rpB2 ⟨L.lab ".Lwc_rodata.x15" + 32, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat
      = true
    rw [rpB2_run, Int64.add_assoc]; exact fx 36 (by simp)
  · exact ldW_rpGH hp hlo hΛ hlab hsite a (o := 36) bl2 rfl (by decide) (by wcfreeH_dec)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hbuf σ0 c0 hJp 8 (.inr rfl)
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 40) (ra := none) (rapc := 0) b3 rfl rpB3_ok hR hRlo hhi
      (by decide) (fun _ _ h => by cases h) (nr (by decide)) (by wcfreeBH_dec) fun σ c _ => ?_
    show freeNH (arun L.lab rpB3 ⟨L.lab ".Lwc_rodata.x15" + 40, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat
      = true
    rw [rpB3_run, Int64.add_assoc]; exact fx 58 (by simp)
  · exact stW_rpGH hp hlo hΛ hlab hsite a (o := 58) bx2 rfl (by decide) (by wcfreeH_dec)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hbuf σ0 c0 hJp 8 (.inr rfl)
  · have hend : ∀ σ c, (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .s4).J σ c →
        (arun L.lab rpB4 ⟨L.lab ".Lwc_rodata.x15" + 62, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc =
          L.lab ".Lscc_rt_main.x2" := by
      rintro σ c ⟨σ0, ⟨c0, hJp⟩, -, hfr⟩
      rw [rpB4_run, hfr.2.2.1, hra σ0 c0 hJp, Int64.ofBitVec_toBitVec]
    refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 62) (ra := some (".Lscc_rt_main.x2", 0))
      (rapc := L.lab ".Lscc_rt_main.x2") b4 rfl rpB4_ok hR hRlo hhi (by decide)
      (fun _ _ h => by cases h; exact (ofNat_zero' _).symm) (Spike.Lib.X64Consumer.hret_of_run rpB4_ok hend)
      (by wcfreeBH_dec) fun σ c hJ => ?_
    show freeNH (arun L.lab rpB4 ⟨L.lab ".Lwc_rodata.x15" + 62, Spike.Lib.X64.Flow.Hello1.oR, σ⟩).pc.toBitVec.toNat
      = true
    rw [hend σ c hJ]; exact freeAt_labH hlab (by wcfreeH_dec)

/-- **`scc_rt_main`'s `.x2` block inside `SFactsSt2` at `ownGH`** (the call
of `wc_main`), in `scc_rt_main`'s region `R`. -/
theorem mB1W_wcGH (a : BitVec 64) (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {σC : Spike.Lib.X64.AS} {Jr : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (mS0 L.lab R σC Jr) mB1 := by
  have hin := Spike.Lib.X64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.X64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, b1⟩, -⟩, -⟩ := hin
  refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 0) (ra := none) (rapc := 0) b1 (ofNat_zero' _) mB1_ok hR hRlo hhi
    (by decide) (fun _ _ h => by cases h)
    (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim) (by wcfreeBH_dec)
    fun σ c _ => ?_
  show freeNH (arun L.lab mB1 ⟨L.lab ".Lscc_rt_main.x2", Spike.Lib.X64.Flow.Hello1.mO, σ⟩).pc.toBitVec.toNat = true
  rw [mB1_run]; exact freeAt_labH hlab (by wcfreeH_dec)

end Inst

end Spike.Lib.X64.HelloPh.WcW

/-- info: 'Spike.Lib.X64.HelloPh.WcW.rdPostW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.rdPostW_wcGH

/-- info: 'Spike.Lib.X64.HelloPh.WcW.mB1W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW.mB1W_wcGH
