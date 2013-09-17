module Everything where

-- A (very abstract) model of small-step supercompilation

import AbstractSc

-- A model of big-step supercompilation

import Util
import AlmostFullRel
import BarWhistles
import Graphs
import GraphsTheorems
import BigStepSc
import BigStepScTheorems
import BigStepScTests
import Cographs
import CographsTheorems
import Statistics

-- An instantiation of the model for counter systems

import BigStepCounters
import Protocol.Synapse
import Protocol.MOSI
import Protocol.MOESI
