#!/usr/bin/env python3
"""Guarded local manuscript pruning. Does not upload or overwrite the original paper.

Usage: python3 verification/prune_manuscript.py INPUT.tex OUTPUT.tex
This targets only HBL_Synchronized_Repair_FiniteProfileClosed_20261027.tex.
It removes one unused auxiliary environment and one obsolete constants subsection.
It does not change the main theorem, essential open tasks, or acceptance percentages.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

EXPECTED_NAME = 'HBL_Synchronized_Repair_FiniteProfileClosed_20261027.tex'
ENV_PATTERN = r'\\begin\{(theorem|proposition|lemma|corollary|verifiedlemma|targettheorem|pendinglemma|pendingproposition|repairprop)\}'
REMOVED_LABELS = {
    'lem:arctan-energy-core-verified',
    'app:proof:lem:M0-constants-stage2', 'lem:M0-constants-stage2',
    'eq:M0-constants-stage2', 'eq:M0-invariant-stage2'
}


def unique_slice(text: str, begin: str, end: str) -> tuple[int, int]:
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError(f'Expected unique anchors: {begin!r}, {end!r}')
    start, stop = text.index(begin), text.index(end)
    if stop <= start: raise ValueError('Section anchors out of order')
    return start, stop


def theorem_count(text: str) -> int:
    return len(re.findall(ENV_PATTERN, text))


def labels(text: str) -> set[str]:
    return set(re.findall(r'\\label\{([^}]+)\}', text))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    if args.source.resolve() == args.output.resolve():
        raise ValueError('Output must be a new file; original manuscript is preserved')
    if args.source.name != EXPECTED_NAME:
        raise ValueError('This patch is pinned to a named manuscript; audit a different version first')
    if args.output.exists(): raise FileExistsError(args.output)
    text = args.source.read_text(encoding='utf-8')
    if theorem_count(text) != 32:
        raise ValueError('Expected 32 theorem-like environments in the reviewed manuscript')
    main_match = re.search(r'\\begin\{targettheorem\}.*?\\end\{targettheorem\}', text, re.S)
    if main_match is None: raise ValueError('Main target theorem not found')
    original_main = main_match.group(0)
    ranges = [
        unique_slice(text,
            r'\begin{verifiedlemma}[有限半径上的实际角变量能量恒等式]',
            r'\begin{verifiedlemma}[实际 Green 与 Birman--Schwinger 算子的正弦模式]'),
        unique_slice(text,
            r'\subsection{慢阈值配对的有限维常数}\label{app:proof:lem:M0-constants-stage2}',
            r'\section{高阶剖面与终端构造的辅助计算}\label{app:profile-terminal-calcs}')
    ]
    removed = [text[start:stop] for start, stop in ranges]
    for start, stop in sorted(ranges, reverse=True):
        text = text[:start]+text[stop:]
    replacements = {
        '这两个辅助结果分别闭合有限标量能量换元和实际 $L^2$ 算子的模式作用。':
            '上述辅助结果给出了实际 $L^2$ 算子的模式作用。',
        r'\section{第一阶慢尾与有限维谱计算}\label{app:slow-finite-calcs}':
            r'\section{第一阶慢尾与相位二次型}\label{app:slow-finite-calcs}',
        '本附录计算慢单极正规形中的若干显式常数，并证明所需的二次型恒等式；这些计算给出一阶剖面消去、阈值平面的加权旋转以及共同二次型谱分裂。':
            '本附录计算慢单极正规形中的仿射尾常数及对数模型的零荷，并记录相位通道的基态变换。'
    }
    for before, after in replacements.items():
        if text.count(before) != 1: raise ValueError(f'Expected unique transition: {before}')
        text = text.replace(before, after)
    original = args.source.read_text(encoding='utf-8')
    if original_main not in text: raise ValueError('Main theorem was changed')
    if theorem_count(text) != 31: raise ValueError('Unexpected final environment count')
    if labels(original)-labels(text) != REMOVED_LABELS:
        raise ValueError('Unexpected labels removed')
    if labels(text)-labels(original): raise ValueError('Unexpected labels added')
    if any(label in text for label in REMOVED_LABELS):
        raise ValueError('Dangling reference to a removed label')
    old_begins = Counter(re.findall(r'\\begin\{([^}]+)\}', original))
    old_ends = Counter(re.findall(r'\\end\{([^}]+)\}', original))
    new_begins = Counter(re.findall(r'\\begin\{([^}]+)\}', text))
    new_ends = Counter(re.findall(r'\\end\{([^}]+)\}', text))
    if old_begins != old_ends or new_begins != new_ends:
        raise ValueError('Environment balance check failed')
    archive = args.output.with_suffix('.removed-sections.tex.txt')
    report_path = args.output.with_suffix('.pruning-audit.json')
    if archive.exists() or report_path.exists(): raise FileExistsError('Audit output already exists')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    archive.write_text('\n\n% --- NEXT REMOVED BLOCK ---\n\n'.join(removed), encoding='utf-8')
    args.output.write_text(text, encoding='utf-8')
    report = {
        'source': str(args.source), 'output': str(args.output),
        'source_sha256': hashlib.sha256(args.source.read_bytes()).hexdigest(),
        'output_sha256': hashlib.sha256(args.output.read_bytes()).hexdigest(),
        'theorem_like_environments_before': 32, 'theorem_like_environments_after': 31,
        'numbered_environments_removed': 0, 'unnumbered_verified_lemmas_removed': 1,
        'standalone_constants_subsections_removed': 1,
        'removed_block_lines': [len(s.splitlines()) for s in removed],
        'removed_labels': sorted(REMOVED_LABELS),
        'main_theorem_byte_content_unchanged': True,
        'main_proof_obligations_removed': 0,
        'newly_verified_original_environments': 0,
        'acceptance_percentage_recomputed': False,
        'latex_compilation_performed': False,
        'removed_text_archive': str(archive)
    }
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
