#!/usr/bin/env bash
rm *.vo
coqc CrushEquality.v &&
coqc MyShortHand.v &&
coqc ProtoSynthDataTypes.v &&
coqc ProtoSynthProtocolDataTypes.v
