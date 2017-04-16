#!/usr/bin/env bash
rm *.vo
coqc CrushEquality.v &&
coqc MyShortHand.v &&
coqc ProtoSynthDataTypes.v &&
coqc ProtoSynthProtocolDataTypes.v &&
coqc TrueProtoSynth.v &&
coqc TrueProtoSynth2.v
