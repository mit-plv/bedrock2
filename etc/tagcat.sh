#!/bin/sh

count() {
	shift
	cat $@
}

count "top-level trace specification" bedrock2/src/bedrock2Examples/lightbulb_spec.v

cd bedrock2/src/bedrock2Examples
count "- SPI driver" SPI.v
count "- ethernet driver" LAN9250.v
count "- lightbulb server" lightbulb.v
cd ../../..

cd bedrock2/src/bedrock2
count "- parsing" NotationsCustomEntry.v
count "- abstract syntax" Syntax.v
count "- parameters and semantics" Semantics.v FE310CSemantics.v Notations.v
count "   - definitions" WeakestPrecondition.v Map/Separation.v TracePredicate.v Lift1Prop.v ReversedListNotations.v
count "   - control flow lemmas" WeakestPreconditionProperties.v TailRecursion.v 
count "   - heap lemmas" ptsto_bytes.v Scalars.v Array.v Memory.v
count "   - proof automation" ProgramLogic.v Map/SeparationLogic.v AbsintWordToZ.v string2ident.v Markers.v
cd ../../..
exit 0

cd compiler/src/compiler
count "- flattening" ExprImp.v FlatImp.v FlattenExpr.v FlattenExprDef.v StringNameGen.v FlattenExprSimulation.v NameGen.v # TODO why so much?
count "- register allocation" RegRename.v
count "- rv32im backend" FlatToRiscvDef.v FlatToRiscvFunctions.v FlatToRiscvCommon.v FlatToRiscvSimulation.v
count "- MMIO" ../compilerExamples/MMIO.v
count "- instruction encoding" EmitsValid.v ../../../deps/riscv-coq/src/riscv/Proofs/*.v
count "- toplevel" PipelineWithRename.v CompilerInvariant.v FitsStack.v ForeverSafe.v Simulation.v MemoryLayout.v
count "- event loop runtime" ToplevelLoop.v RiscvEventLoop.v
count "- proof automation" SeparationLogic.v SimplWordExpr.v DivisibleBy4.v Simp.v mod4_0.v Rem4.v on_hyp_containing.v eqexact.v
cd ../../..

count "- risc-v spec (not discussed here)" deps/riscv-coq/src/riscv/Spec/*.v deps/riscv-coq/src/riscv/Platform/Memory.v
count "- MMIO \"platform\" model & lemmas" deps/riscv-coq/src/riscv/Platform/FE310ExtSpec.v deps/riscv-coq/src/riscv/Platform/MinimalMMIO.v deps/riscv-coq/src/riscv/Platform/Sane.v
count "- i-cache lemmas" deps/riscv-coq/src/riscv/Platform/RiscvMachine.v

cd processor/src/processor
count "- fetch" KamiProc.v KamiRiscv.v
count "- decode & exec" KamiRiscvStep.v KamiWord.v DecExecOk.v ../../../end2end/src/end2end/KamiRiscvWordProperties.v
count "- top-level simulation" KamiProc.v KamiRiscv.v
cd ../../..

count "glue proof" end2end/src/end2end/Bedrock2SemanticsForKami.v end2end/src/end2end/End2EndPipeline.v end2end/src/end2end/End2EndLightbulb.v
count "utilities we wish were in Coq standard library" deps/coqutil
