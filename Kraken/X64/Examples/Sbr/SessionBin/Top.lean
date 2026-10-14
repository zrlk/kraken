import Kraken.X64.Examples.Sbr.SessionBin.InitSafe
import Kraken.X64.Examples.Sbr.SessionBin.TopCalls

/-!
# A decoding session over the binary: the headline

`sbr_session_safe`: for the linked machine code of FFmpeg's SBR decoder (`aacsbr.o` with its
callees), given the layout of the link (`SbrBinary`), the contracts of the external routines
(`InitExt`) and a 32-bit bound on their stack, every entry point is safe in every session:

* `ff_aac_sbr_ctx_alloc_init` returns; on `0` the element it allocated is `Live`;
* `ff_aac_sbr_decode_extension`, `ff_aac_sbr_decode_usac_data`, `ff_aac_sbr_config_usac` on a
  `Live` element return with it `Live` again (`Ready` when the parse succeeded), or (the two
  parsers) stop at FFmpeg's `abort`/bounds trap (`Traps`);
* `ff_aac_sbr_apply` on a `Ready` element returns with it `Ready` and the output written.

Every run stays in the memory it owns (the separation-logic pre/postconditions), returns to its
caller with the ABI's callee-saved registers, and uses at most the stated stack. The vocabulary
is in `TopDefs`; the four restatements are in `TopCalls`; init's is in `InitSafe`.

The Huffman tables are FFmpeg's (`Setup.vs`, `Setup.vp`); their prefix-code and bound facts are
proved (`VlcWit`), not assumed.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Init

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- **The binary**: the placement of every text (init, the parser, apply's cluster) and the
layout facts of the link. Not proved; the evidence is the re-assembly check of the texts
against the objects. -/
abbrev SbrBinary : Prop := SessPlaced

/-- `ff_aac_sbr_ctx_alloc_init(ac, che, id)`: with the caller's `ac` fields, `ac->fdsp`, the
static data and init's state, the call returns; on `0` the element at the new `*che` is live. -/
def InitSafe (S : Setup) (X : Mem 64 → Prop) : Prop :=
  ∀ {avctx fdsp : BitVec 64} {er ps : BitVec 32} {Rest : Mem 64 → Prop} {ra : Int64}
    {t : MachineData},
    InitPre S.k S.env.TxTab X (InitOwn S (arg0 t) avctx fdsp er ps Rest) ra t →
    Ends "ff_aac_sbr_ctx_alloc_init" t ra (InitQ S X Rest avctx fdsp er ps ra t) NoStops

/-- `ff_aac_sbr_decode_extension(ac, che, gb, crc, cnt, id)` on a live element: returns `cnt`
with the element ready, the reader advanced within its bound, the caller's objects given back
(`ext_sample_rate` possibly set); or stops at a trap. -/
def DecSafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {b : Rdr} {i : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData},
    DecCall che ac b i t →
    CallPre (decStack S.k) (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ DecObj b avctx Rc i t))
      ra t →
    Ends "ff_aac_sbr_decode_extension" t ra (fun s => ∃ (i' : BitVec 32) (er' : BitVec 32),
      i'.toNat ≤ b.r.p8.toNat ∧ ret32 s = (arg4 t).setWidth 32
      ∧ CallPost (decStack S.k)
        (Ready S che ac ⋆ (AcFields ac avctx er' ps ⋆ DecObj b avctx Rc i' t)) ra t s) Traps

/-- `ff_aac_sbr_decode_usac_data(ac, che, ue, gb, …)` on a live element: returns with the
element live (ready if it returned `0`), the reader advanced within its bound, the caller's
objects given back; or stops at a trap. -/
def UsacSafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {u : UsacIn} {i : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData},
    UsacCall che ac u i t →
    CallPre (usacStack S.k)
      (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ UsacObjects u che ac Rc i)) ra t →
    Ends "ff_aac_sbr_decode_usac_data" t ra (fun s => ∃ i' : BitVec 32,
      i'.toNat ≤ u.p8.toNat
      ∧ CallPost (usacStack S.k) (ElemState S che ac (decide (ret32 s = 0#32))
        ⋆ (AcFields ac avctx er ps ⋆ UsacObjects u che ac Rc i')) ra t s) Traps

/-- `ff_aac_sbr_config_usac(ac, che, ue)` on a live element: returns `0` with the element
ready (switched off) and the caller's objects given back. -/
def ConfigSafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop} {ra : Int64}
    {t : MachineData},
    ConfigCall che ac t →
    CallPre 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t →
    Ends "ff_aac_sbr_config_usac" t ra (fun s => ret32 s = 0#32
      ∧ CallPost 0 (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t s) NoStops

/-- `ff_aac_sbr_apply(ac, che, id, L, R)` on a ready element: returns with the element ready,
the output buffers and the caller's objects given back. -/
def ApplySafe (S : Setup) : Prop :=
  ∀ {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop} {ra : Int64}
    {t : MachineData},
    ApplyCall che ac t →
    CallPre (applyStack S.k) (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc)))
      ra t →
    Ends "ff_aac_sbr_apply" t ra (fun s => CallPost (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t s) NoStops

/-- **The SBR decoder's binary is safe in every session.** Given the link's layout, the
external routines' contracts at the caller's environment, and their stack `S.k` within a
32-bit offset of `sbr_reset`'s frame, every entry point meets its contract. -/
theorem sbr_session_safe (B : SbrBinary) (S : Setup) (X : Mem 64 → Prop) (hx : InitExt S X)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) :
    InitSafe S X ∧ DecSafe S ∧ UsacSafe S ∧ ConfigSafe S ∧ ApplySafe S :=
  ⟨fun hpre => init_safe B.init hx hpre, fun hc hm => dec_top B S hk hc hm,
    fun hc hm => usac_top B S hk hc hm, fun hc hm => config_top B S hc hm,
    fun hc hm => apply_top B S hk hc hm⟩

end Kraken.Examples.Sbr.SessionBin
