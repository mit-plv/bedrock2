#!/bin/sh

count() {
	printf "%s: " "$1"
	shift
	cloc --include-lang=Coq --json $@ | jq .Coq.code
}

count "top-level trace specification" bedrock2/src/bedrock2Examples/lightbulb_spec.v

cd bedrock2/src/bedrock2Examples
printf "software:\n"
count "- SPI driver" SPI.v
count "- ethernet driver" LAN9250.v
count "- lightbulb server" lightbulb.v
cd ../../..

cd bedrock2/src/bedrock2
printf "language:\n"
count "- parsing" NotationsCustomEntry.v StructNotations.v Structs.v
count "- abstract syntax" Syntax.v
count "- parameters and semantics" Semantics.v FE310CSemantics.v Notations.v
printf "  program logic:\n"
count "   - definitions" WeakestPrecondition.v Map/Separation.v TracePredicate.v Lift1Prop.v ReversedListNotations.v
count "   - control flow lemmas" WeakestPreconditionProperties.v TailRecursion.v 
count "   - heap lemmas" ptsto_bytes.v Scalars.v Array.v Memory.v
count "   - proof automation" ProgramLogic.v Map/SeparationLogic.v AbsintWordToZ.v string2ident.v Markers.v
cd ../../..

cd compiler/src/compiler
printf "compiler:\n"
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
count "- fetch" KamiProc.v KamiRiscv.v
count "- decode & exec" KamiRiscvStep.v KamiWord.v DecExecOk.v ../../../end2end/src/end2end/KamiRiscvWordProperties.v
count "- top-level simulation" KamiProc.v KamiRiscv.v
printf "%s\n" "- pipeline correctess proof is described in Kami ICFP paper (repo weighs 50k lines?)"
cd ../../..
printf "%s " "- HDL specification" ; coqwc deps/kami/Kami/Semantics.v | tail -1 | cut -d ' ' -f7

count "glue proof" end2end/src/end2end/Bedrock2SemanticsForKami.v end2end/src/end2end/End2EndPipeline.v end2end/src/end2end/End2EndLightbulb.v
printf "FPGA glue (Verilog): "; cloc --json processor/integration/system.v  | jq '.["Verilog-SystemVerilog"].code'
count "utilities we wish were in Coq standard library" deps/coqutil

printf "\n"
printf "note: these counts do NOT add up to the whole git repo because the same repository contains other experiments on the same tool that are not necessary for the case study described here, and we omitted all files that exclusively benefit those experiments from the counts above\n"
