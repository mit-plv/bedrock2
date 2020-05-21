#!/bin/sh
DIR="$(dirname "$(readlink -f "$0")")"

count() {
	printf "%s: " "$1"
	shift
	cat $@ | python3 "$DIR/tagcount.py"
}

count "top-level trace specification" bedrock2/src/bedrock2Examples/lightbulb_spec.v

cd bedrock2/src/bedrock2Examples
count "- software" SPI.v LAN9250.v lightbulb.v
cd ../../..

cd bedrock2/src/bedrock2
count "- program logic" WeakestPrecondition.v Map/Separation.v TracePredicate.v Lift1Prop.v ReversedListNotations.v FE310CSemantics.v Notations.v \
  WeakestPreconditionProperties.v TailRecursion.v \
  ProgramLogic.v Map/SeparationLogic.v AbsintWordToZ.v string2ident.v Markers.v \
  ptsto_bytes.v Scalars.v Array.v Memory.v
cd ../../..

cd compiler/src/compiler
printf "compiler:\n"
count "- parsing" ../../../bedrock2/src/bedrock2/{Syntax.v,NotationsCustomEntry.v}
count "- semantics" ../../../bedrock2/src/bedrock2/Semantics.v
count "- flattening" ExprImp.v FlatImp.v FlattenExpr.v FlattenExprDef.v StringNameGen.v FlattenExprSimulation.v NameGen.v # TODO why so much?
count "- register allocation" RegRename.v
count "- rv32im backend" FlatToRiscvDef.v FlatToRiscvFunctions.v FlatToRiscvCommon.v FlatToRiscvSimulation.v
count "- MMIO" ../compilerExamples/MMIO.v
count "- instruction encoding" EmitsValid.v ../../../deps/riscv-coq/src/riscv/Proofs/*.v
count "- toplevel" PipelineWithRename.v CompilerInvariant.v FitsStack.v ForeverSafe.v Simulation.v MemoryLayout.v
count "- event loop runtime" ToplevelLoop.v RiscvEventLoop.v
count "- proof automation" SeparationLogic.v SimplWordExpr.v DivisibleBy4.v Simp.v mod4_0.v Rem4.v on_hyp_containing.v eqexact.v
cd ../../..

printf "instruction set:\n"
count "- risc-v spec (not discussed here)" deps/riscv-coq/src/riscv/Spec/*.v deps/riscv-coq/src/riscv/Platform/Memory.v
count "- MMIO \"platform\" model & lemmas" deps/riscv-coq/src/riscv/Platform/FE310ExtSpec.v deps/riscv-coq/src/riscv/Platform/MinimalMMIO.v deps/riscv-coq/src/riscv/Platform/Sane.v
count "- i-cache lemmas" deps/riscv-coq/src/riscv/Platform/RiscvMachine.v

cd processor/src/processor
printf "processor rv32im proof:\n"
count "- decode & exec" KamiRiscvStep.v KamiWord.v DecExecOk.v ../../../end2end/src/end2end/KamiRiscvWordProperties.v
count "- top-level simulation" KamiRiscv.v KamiProc.v Consistency.v
printf "%s\n" "- pipeline correctess proof is described in Kami ICFP paper (repo weighs 50k lines?)"
cd ../../..
printf "%s " "- HDL specification" ; coqwc deps/kami/Kami/Semantics.v | tail -1 | cut -d ' ' -f7

count "glue proof" end2end/src/end2end/Bedrock2SemanticsForKami.v end2end/src/end2end/End2EndPipeline.v end2end/src/end2end/End2EndLightbulb.v
printf "FPGA glue (Verilog): "; cloc --json processor/integration/system.v  | jq '.["Verilog-SystemVerilog"].code'
count "utilities we wish were in Coq standard library" deps/coqutil

printf "\n"
printf "note: these counts do NOT add up to the whole git repo because the same repository contains other experiments on the same tool that are not necessary for the case study described here, and we omitted all files that exclusively benefit those experiments from the counts above\n"
