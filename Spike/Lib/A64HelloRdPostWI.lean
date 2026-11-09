/-
**hello.w's `wc_rodata` from the allocator's return, and `scc_rt_main`'s `.sp0`
block, inside `SFactsSt2` at `ownGH`** (AArch64): the
`SFactsSt2` component of `HelloRd.RdPostW` (`.sp0`'s blocks, the two exchanges'
loads and stores at the buffer, the publish fence, the return to
`scc_rt_main`'s `.sp0`) and of `HelloM.MainPostW.sp0` (`Hello1.mB1`, up to
`bl wc_main`). Each node is `Rt.blkW_pre`/`nodeW_*_pre` at `instOkH`, moved to
`ownGH` at its free pcs; the phase facts are decided by the kernel against
helloProg's labels (`rpTabH`).

- `rpTabH`, `rpFactsH`, `rpW_factH`: the blocks' phase facts.
- `blkW_rpGH`: a covered block of `rpTabH`, its `ret`s to `rapc` (`hret`).
- `mapped_rd`: a word mapped for writing is mapped for reading.
- `ldW_rpGH`, `stW_rpGH`, `fenW_rpGH`: a load or store at a buffer word
  `BoxOkH`, the fence.
- `rdPostW_wcGH`: `RdPostW` at `SFactsSt2`/`ownGH`, the buffer's two words
  `BoxOkH` at `.sp0` (`hbuf`), the saved return address `scc_rt_main`'s `.sp0`
  (`hra`).
- `mB1W_wcGH`: `scc_rt_main`'s `.sp0` block at `SFactsSt2`/`ownGH`.
-/
import Spike.Lib.A64HelloRdPreWI
import Spike.Lib.A64HelloMain

namespace Spike.Lib.A64.HelloPh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At ofNat4_zero ofNat4_succ)
open Spike.Lib.A64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)
open Spike.Lib.A64.HelloPh
open Spike.Lib.A64.WakePh.WcW (blkW_mapC c0N_cfacts nodeW_dmb_pre NodeW.ofAll)
open Spike.Lib.A64.Flow.WakeWc (pubF_eq)
open Spike.Lib.A64.Flow.HelloRd (pN RdPostW rpIn hello_rpIn)
open Spike.Lib.A64.Flow.Hello1 (rdFr rpB0 rpB0_ok rpB0_run rpB1 rpB1_ok rpB1_run rpB2 rpB2_ok rpB2_run rpB3
  rpB3_ok rpB3_run rpB4 rpB4_ok rpB4_run rAddr_x10_x0 mB1 mB1_ok mB1_run mS0 mR)

/-! ## The blocks' phase facts -/

/-- **`.sp0`'s blocks and single instructions, and `scc_rt_main`'s `.sp0` block**:
the last block of `wc_rodata` returns to `scc_rt_main`'s `.sp0`. -/
def rpTabH : List PhFact :=
  [.blk ".L19_wc_rodata.sp0" 0 rpB0 none none,
   .step ".L19_wc_rodata.sp0" 2,
   .blk ".L19_wc_rodata.sp0" 3 rpB1 none none,
   .step ".L19_wc_rodata.sp0" 9,
   .blk ".L19_wc_rodata.sp0" 10 rpB2 none none,
   .step ".L19_wc_rodata.sp0" 11,
   .blk ".L19_wc_rodata.sp0" 12 rpB3 none none,
   .step ".L19_wc_rodata.sp0" 17,
   .step ".L19_wc_rodata.sp0" 18,
   .blk ".L19_wc_rodata.sp0" 19 rpB4 (some ".L1_scc_rt_main.sp0") none,
   .blk ".L1_scc_rt_main.sp0" 0 mB1 none none]

/-- **The blocks' facts hold** at `phC`. -/
theorem rpFactsH : rpTabH.all (factOk (codeT lo SccCode.helloProg) okC phC) = true := by
  decide +kernel

/-- **A fact of `rpTabH` at `phH`.** -/
theorem rpW_factH {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {f : PhFact}
    (hf : f ∈ rpTabH) : factOk (codeOf lo SccCode.helloProg) (okPcOf lo SccCode.helloProg Λ) phH f = true := by
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
theorem blkW_rpGH (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int} {ra : Option String} {rapc : Int64}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH) (hra : ∀ r, ra = some r → rapc = L.lab r)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = rapc)
    (hfree : freeAtH l k blk.length = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.A64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := rapc) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (rpW_factH hΛ hf)
  have hW := Spike.Lib.A64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hal hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun σ _ hJ => let ⟨c', hJ'⟩ := hJ.2; hret σ c' hJ') (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := Spike.Lib.A64.Flow.code_of L.lays rfl (hp ▸ hb) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hal hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeAt_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- **A block split by a return label** (`m`, after
its first `jA` rows; `blockAcross`): as `blkW_rpGH`. -/
theorem blkW_rpGHA (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (a : BitVec 64)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    {n : ND} {blk : List Directive} {l m : Label} {k jA : Nat} {blo bhi : Int} {ra : Option String} {rapc : Int64}
    (hb : Scc.Cert.Rt.A64.blockAcross SccCode.helloProg l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hf : PhFact.blk l k blk ra none ∈ rpTabH) (hra : ∀ r, ra = some r → rapc = L.lab r)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = rapc)
    (hfree : freeAtH l k blk.length = true)
    (hlast : ∀ σ c, n.J σ c →
      freeNH (Spike.Lib.A64.Flow.arun L.lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n blk := by
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.A64Consumer.c0 ∧ ∃ c', n.J σ c'⟩
  have hph := blkPh_of_factOk hlab (rapc := rapc) (dset := fun _ => false) hra
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h) (rpW_factH hΛ hf)
  have hW := Spike.Lib.A64.Rt.blkW_preA (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ)
    (lbl := fun _ => none) (rS := rS) (F := F) (n := n') (hp ▸ hb) he hok hR hal hlo' hhi
    (fun _ _ hJ => hJ.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0) hph
    (fun σ _ hJ => let ⟨c', hJ'⟩ := hJ.2; hret σ c' hJ') (fun _ _ _ => rfl)
    (fun _ _ h => h)
  have hcode := Spike.Lib.A64.code_field_blockAcross L.lays rfl (hp ▸ hb)
    (List.take_append_drop jA blk) (q := n.pc) he
  have hag := blkAgreeWH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (n := n') hlab hcode hok hR hal hlo' hhi
    hsite (fun j hj => by rw [← he]; exact freeAt_pcH hlab hfree hj)
    (fun σ c hJ => let ⟨_, hJ'⟩ := hJ.2; hlast σ _ hJ')
  have h2 := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hW) hag
  exact blkW_mapC (n' := n') rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- The pc `4 k` past `.sp0`, `k < 20`, is free. -/
theorem freeSp0H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {k : Nat}
    (hk : k < 20) : freeNH (L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * k)).toBitVec.toNat = true := by
  have := freeAt_pcH hlab (l := ".L19_wc_rodata.sp0") (k := 0) (n := 20) (by free_decH) hk
  rwa [ofNat4_zero] at this

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hΛ hlab hsite

/-- **A load `ldr x9, [x10, #i]` at `.sp0 + 4 k` of a word `BoxOkH`** inside
`SFactsSt2` at `ownGH`: its address `A σ` at every state (`ha`), `BoxOkH` there
(`hbox`). -/
theorem ldW_rpGH (a : BitVec 64) {n : ND} {i : Int64} {k : Nat} (hk : k + 1 < 20)
    (hb : blockAt SccCode.helloProg ".L19_wc_rodata.sp0" k [Spike.Lib.A64.Flow.ldrDir .X9 .X10 i] = true)
    (he : n.pc = L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * k))
    (hf : PhFact.step ".L19_wc_rodata.sp0" k ∈ rpTabH)
    (hbox : ∀ σ c, n.J σ c → BoxOkH Λ L a F (Spike.Lib.A64.Flow.rAddr σ.regs .X10 i)) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hs := step_of_factOk hlab (rpW_factH hΛ hf)
  refine NodeW.ofAll (fun σ => Spike.Lib.A64.Flow.rAddr σ.regs .X10 i) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    exact absurd (hbox σ c hJ) hA
  obtain ⟨hmw, hun, -⟩ := hA
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.A64.Rt.nodeW_ldr_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
      (lbl := fun _ => none) (by rw [hp]; exact hb) rfl he c0N_cfacts hs.1 (fun _ _ h => h) hs.2 ?_
      (mapped_rd hmw) hun) (by rw [he]; exact freeSp0H hlab (by omega)) ?_ ?_
  · rintro σ c ⟨-, c', -, rfl⟩
    rfl
  · rw [he, show L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * k) + Int64.ofNat 4 =
      L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * (k + 1)) from by rw [ofNat4_succ]; rfl]
    exact freeSp0H hlab hk
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, hJ, hsA⟩
    have hc := cell1H hp hb h1 h2 (by rw [h4', he])
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 i = A := by rw [hAb.regs, hsA]
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_ldr hc ha' (hun _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **A store `str x9, [x10, #i]` at `.sp0 + 4 k` of a word `BoxOkH`** inside
`SFactsSt2` at `ownGH` (as `ldW_rpGH`). -/
theorem stW_rpGH (a : BitVec 64) {n : ND} {i : Int64} {k : Nat} (hk : k + 1 < 20)
    (hb : blockAt SccCode.helloProg ".L19_wc_rodata.sp0" k [Spike.Lib.A64.Flow.strDir .X9 .X10 i] = true)
    (he : n.pc = L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * k))
    (hf : PhFact.step ".L19_wc_rodata.sp0" k ∈ rpTabH)
    (hbox : ∀ σ c, n.J σ c → BoxOkH Λ L a F (Spike.Lib.A64.Flow.rAddr σ.regs .X10 i)) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hs := step_of_factOk hlab (rpW_factH hΛ hf)
  refine NodeW.ofAll (fun σ => Spike.Lib.A64.Flow.rAddr σ.regs .X10 i) fun A => ?_
  by_cases hA : BoxOkH Λ L a F A
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    exact absurd (hbox σ c hJ) hA
  obtain ⟨hmw, hun, hno⟩ := hA
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (Spike.Lib.A64.Rt.nodeW_st_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
      (lbl := fun _ => none) (ownOf := ownH L a) (fun _ => rfl) (by rw [hp]; exact hb) rfl he c0N_cfacts hs.1
      (fun _ _ h => h) hs.2 ?_ hmw hun hno) (by rw [he]; exact freeSp0H hlab (by omega)) ?_ ?_
  · rintro σ c ⟨-, c', -, rfl⟩
    rfl
  · rw [he, show L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * k) + Int64.ofNat 4 =
      L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * (k + 1)) from by rw [ofNat4_succ]; rfl]
    exact freeSp0H hlab hk
  · rintro s c ⟨h1, h2, h3', h4', σ, hAb, hF, hJ, hsA⟩
    have hc := cell1H hp hb h1 h2 (by rw [h4', he])
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs .X10 i = A := by rw [hAb.regs, hsA]
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_str hc ha' (hun _ hF), fun s' hu => ?_⟩
    · cases h
    · rw [h3', EvTree.access_empty] at hu
      obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **The publish fence at `.sp0 + 72`** inside `SFactsSt2` at `ownGH`. -/
theorem fenW_rpGH (a : BitVec 64) {n : ND} (he : n.pc = L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 18)) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F n := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨-, h18⟩, -⟩ := hin
  rw [pubF_eq] at h18
  have hf := step_of_factOk hlab (rpW_factH hΛ (f := .step ".L19_wc_rodata.sp0" 18) (by decide))
  refine nodeW_wcGH (TkW := fun _ => False) (rS := rS) hlab hsite
    (nodeW_dmb_pre (instOkH hp hlo a (fun _ => False) hsite (rS := rS)) (Λ := Λ) (rS := rS)
    (lbl := fun _ => none) (by rw [hp]; exact h18) rfl he c0N_cfacts hf.1 (fun _ _ h => h) hf.2)
    (by rw [he]; exact freeSp0H hlab (by decide)) ?_ ?_
  · rw [he, show L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 18) + Int64.ofNat 4 =
      L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19) from by rw [ofNat4_succ (k := 18)]; rfl]
    exact freeSp0H hlab (by decide)
  · rintro s c ⟨h1, h2, -, h4', -⟩
    have hc := cell1H hp h18 h1 h2 (by rw [h4', he])
    refine ⟨_, _, hc, fun imm h => ?_, Kraken.Promising.Lower.A64.exec_dmb hc, fun s' hu => ?_⟩
    · cases h
    · obtain ⟨_, hu⟩ := hu
      simp only [TreeLeaf] at hu
      subst hu; rfl

/-- **`RdPostW` inside `SFactsSt2` at `ownGH`** (owned word `a`), none moved by
the take: the buffer's two words `BoxOkH` at every `.sp0` state (`hbuf`), the
saved return address `scc_rt_main`'s `.sp0` (`hra`). -/
theorem rdPostW_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) {Jp Jp' J1 J2 J2' J3 J4 J5 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      BoxOkH Λ L a F (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 i))
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot (-8) = (L.lab ".L1_scc_rt_main.sp0").toBitVec) :
    RdPostW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F Jp Jp' J1 J2 J2' J3 J4 J5 := by
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨b0, bl1⟩, b1⟩, bx1⟩, b2⟩, bl2⟩, b3⟩, bx2⟩, -⟩, b4⟩ := hin
  have nr : ∀ {blk : List Directive}, Spike.Lib.A64Consumer.noRetBlk blk = true → ∀ {n : ND},
      ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun L.lab (blk.take j) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = 0 :=
    fun hnr _ _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hnr j hj r hr).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 0) (ra := none) b0 (ofNat4_zero _) rpB0_ok hR hal hRlo hhi
      (by decide) (fun _ h => by cases h) (nr (by decide)) (by free_decH) fun σ c _ => ?_
    show freeNH (Spike.Lib.A64.Flow.arun L.lab rpB0 ⟨L.lab ".L19_wc_rodata.sp0", ⟨-48, []⟩, σ⟩).pc.toBitVec.toNat
      = true
    rw [rpB0_run, ← Spike.Lib.A64.Rt.MainU.pc2]; exact freeSp0H hlab (by decide)
  · exact ldW_rpGH hp hlo hΛ hlab hsite a (k := 2) (by decide) bl1 rfl (by decide)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ => by rw [rAddr_x10_x0 hx]; exact hbuf σ0 c0 hJp 0 (.inl rfl)
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 3) (ra := none) b1 rfl rpB1_ok hR hal hRlo hhi
      (by decide) (fun _ h => by cases h) (nr (by decide)) (by free_decH) fun σ c _ => ?_
    show freeNH (Spike.Lib.A64.Flow.arun L.lab rpB1
      ⟨L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 3), ⟨-48, []⟩, σ⟩).pc.toBitVec.toNat = true
    rw [rpB1_run, show ∀ x : Int64, x + Int64.ofNat (4 * 3) + 4 + 4 + 4 + 4 + 4 + 4 = x + Int64.ofNat (4 * 9)
      from fun x => by simp only [Int64.add_assoc]; rfl]
    exact freeSp0H hlab (by decide)
  · exact stW_rpGH hp hlo hΛ hlab hsite a (k := 9) (by decide) bx1 rfl (by decide)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [rAddr_x10_x0 hx]; exact hbuf σ0 c0 hJp 0 (.inl rfl)
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 10) (ra := none) b2 rfl rpB2_ok hR hal hRlo hhi
      (by decide) (fun _ h => by cases h) (nr (by decide)) (by free_decH) fun σ c _ => ?_
    show freeNH (Spike.Lib.A64.Flow.arun L.lab rpB2
      ⟨L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 10), ⟨-48, []⟩, σ⟩).pc.toBitVec.toNat = true
    rw [rpB2_run, ← ofNat4_succ]; exact freeSp0H hlab (by decide)
  · exact ldW_rpGH hp hlo hΛ hlab hsite a (k := 11) (by decide) bl2 rfl (by decide)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ => by rw [rAddr_x10_x0 hx]; exact hbuf σ0 c0 hJp 8 (.inr rfl)
  · refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 12) (ra := none) b3 rfl rpB3_ok hR hal hRlo hhi
      (by decide) (fun _ h => by cases h) (nr (by decide)) (by free_decH) fun σ c _ => ?_
    show freeNH (Spike.Lib.A64.Flow.arun L.lab rpB3
      ⟨L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 12), ⟨-48, []⟩, σ⟩).pc.toBitVec.toNat = true
    rw [rpB3_run, show ∀ x : Int64, x + Int64.ofNat (4 * 12) + 4 + 4 + 4 + 4 + 4 = x + Int64.ofNat (4 * 17)
      from fun x => by simp only [Int64.add_assoc]; rfl]
    exact freeSp0H hlab (by decide)
  · exact stW_rpGH hp hlo hΛ hlab hsite a (k := 17) (by decide) bx2 rfl (by decide)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [rAddr_x10_x0 hx]; exact hbuf σ0 c0 hJp 8 (.inr rfl)
  · exact fenW_rpGH hp hlo hΛ hlab hsite a rfl
  · have hend : ∀ σ c, (pN L.lab Jp Jp' J1 J2 J2' J3 J4 J5 .s4).J σ c →
        (Spike.Lib.A64.Flow.arun L.lab rpB4
          ⟨L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19), ⟨-48, []⟩, σ⟩).pc = L.lab ".L1_scc_rt_main.sp0" := by
      rintro σ c ⟨σ0, ⟨c0, hJp⟩, -, -, -, h8⟩
      rw [rpB4_run, h8, hra σ0 c0 hJp, Int64.ofBitVec_toBitVec]
    refine blkW_rpGHA hp hlo hΛ hlab a hsite (k := 19) (ra := some ".L1_scc_rt_main.sp0") b4 rfl rpB4_ok hR hal
      hRlo hhi (by decide) (fun _ h => by cases h; rfl) (Spike.Lib.A64Consumer.hret_of_run rpB4_ok hend)
      (by free_decH) fun σ c hJ => ?_
    show freeNH (Spike.Lib.A64.Flow.arun L.lab rpB4
      ⟨L.lab ".L19_wc_rodata.sp0" + Int64.ofNat (4 * 19), ⟨-48, []⟩, σ⟩).pc.toBitVec.toNat = true
    rw [hend σ c hJ]; exact freeAt_labH hlab (by free_decH)

/-- **`scc_rt_main`'s `.sp0` block inside `SFactsSt2` at `ownGH`** (the call
of `wc_main`), in `scc_rt_main`'s region `R`. -/
theorem mB1W_wcGH (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) {σC : Spike.Lib.A64.Flow.AS} {Jr : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s) (Spike.Lib.A64.PhRec.K L rS)
      L.exe L.endPc R F (mS0 L.lab R σC Jr) mB1 := by
  have hin := Spike.Lib.A64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.A64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, b1⟩, -⟩, -⟩ := hin
  refine blkW_rpGH hp hlo hΛ hlab a hsite (k := 0) (ra := none) (rapc := 0) b1 (ofNat4_zero _) mB1_ok hR hal hRlo hhi
    (by decide) (fun _ h => by cases h)
    (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim) (by free_decH)
    fun σ c _ => ?_
  show freeNH (Spike.Lib.A64.Flow.arun L.lab mB1 ⟨L.lab ".L1_scc_rt_main.sp0", ⟨-80, []⟩, σ⟩).pc.toBitVec.toNat
    = true
  rw [mB1_run]; exact freeAt_labH hlab (by free_decH)

end Inst

end Spike.Lib.A64.HelloPh.WcW

/-- info: 'Spike.Lib.A64.HelloPh.WcW.rdPostW_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.rdPostW_wcGH

/-- info: 'Spike.Lib.A64.HelloPh.WcW.mB1W_wcGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcW.mB1W_wcGH
