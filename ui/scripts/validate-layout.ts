import {layoutCandidates} from "../benchmarks/candidates";
import {runSyntheticSeed} from "../benchmarks/synthetic-suite";

function argument(name: string) {
  const prefix = `--${name}=`;
  return process.argv.find((value) => value.startsWith(prefix))?.slice(prefix.length);
}

const candidateId = argument("candidate") ?? "failed-baseline";
const suite = argument("suite") ?? "smoke";
const candidate = layoutCandidates.get(candidateId);
if (!candidate) {
  throw new Error(
    `Unknown candidate ${candidateId}; available: ${[...layoutCandidates.keys()].join(", ")}`,
  );
}
const seeds =
  suite === "tuning"
    ? Array.from({length: 10}, (_, index) => index)
    : suite === "holdout"
      ? Array.from({length: 20}, (_, index) => 1000 + index)
      : [0];
const results = seeds.map((seed) =>
  runSyntheticSeed(candidate, seed, {includeScale: suite !== "smoke"}),
);
const output = {
  candidate: candidate.id,
  description: candidate.description,
  suite,
  seeds,
  purpose:
    "Diagnostic observations only; synthetic labels and numeric values do not define completion.",
  results,
};
console.log(JSON.stringify(output, null, 2));
