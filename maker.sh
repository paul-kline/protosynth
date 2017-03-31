#!/usr/bin/env bash
rm *.vo
coqc MyShortHand.v &&
coqc ProtoSynthDataTypes.v &&
coqc ProtoSynthProtocolDataTypes.v &&
coqc ProtoSynthDataTypeEqualities.v

