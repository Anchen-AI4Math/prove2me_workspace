import sys
import inspect_author as p
import run_phase1 as engine
sys.stdout.reconfigure(encoding='utf-8')
plan=p.load(p.OUT/'lossless-encoder-preparation.json'); p.check([plan['source'],plan['snapshot'],plan['selection']])
engine.build('independent-lossless-encoder','PFIndependentLosslessEncoderV1','PFIndependentLosslessEncoderV1.lean')
