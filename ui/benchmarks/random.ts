export type DeterministicRandom = {
  next: () => number;
  integer: (upperExclusive: number) => number;
  pick: <T>(values: readonly T[]) => T;
  shuffle: <T>(values: readonly T[]) => T[];
};

/** Mulberry32 is used only to generate repeatable benchmark data and samples. */
export function deterministicRandom(seed: number): DeterministicRandom {
  let state = seed >>> 0;
  const next = () => {
    state += 0x6d2b79f5;
    let value = state;
    value = Math.imul(value ^ (value >>> 15), value | 1);
    value ^= value + Math.imul(value ^ (value >>> 7), value | 61);
    return ((value ^ (value >>> 14)) >>> 0) / 4294967296;
  };
  const integer = (upperExclusive: number) =>
    Math.floor(next() * Math.max(1, upperExclusive));
  const pick = <T>(values: readonly T[]) => values[integer(values.length)];
  const shuffle = <T>(values: readonly T[]) => {
    const result = [...values];
    for (let index = result.length - 1; index > 0; index -= 1) {
      const other = integer(index + 1);
      [result[index], result[other]] = [result[other], result[index]];
    }
    return result;
  };
  return {next, integer, pick, shuffle};
}

