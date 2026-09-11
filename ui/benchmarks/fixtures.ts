import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
} from "../lib/specification-layout";
import {deterministicRandom} from "./random";
import type {FixtureRole, LayoutFixture} from "./types";

type FixtureBuilder = {
  nodes: SpecificationLayoutInputNode[];
  edges: SpecificationLayoutInputEdge[];
  specificationIds: string[];
  roles: Map<string, FixtureRole>;
};

function builder(): FixtureBuilder {
  return {nodes: [], edges: [], specificationIds: [], roles: new Map()};
}

function addSpecification(
  fixture: FixtureBuilder,
  id: string,
  statement: string,
  role: FixtureRole,
) {
  fixture.nodes.push({
    id,
    nodeKind: "specification",
    statement,
    radius: 4,
    visible: true,
  });
  fixture.specificationIds.push(id);
  fixture.roles.set(id, role);
}

function addTerm(
  fixture: FixtureBuilder,
  id: string,
  members: readonly string[],
) {
  fixture.nodes.push({
    id,
    nodeKind: "term",
    statement: id,
    radius: 3,
    visible: false,
  });
  for (const member of members) {
    fixture.edges.push({
      id: `${id}:${member}`,
      source: member,
      target: id,
      current: true,
      family: "lexical",
    });
  }
}

function addSemantic(
  fixture: FixtureBuilder,
  id: string,
  source: string,
  target: string,
) {
  fixture.edges.push({
    id,
    source,
    target,
    current: true,
    family: "semantic",
  });
}

function vocabulary(seed: number, context: number, channel: number) {
  return `lex${seed}x${context}q${channel}`;
}

function addContext(
  fixture: FixtureBuilder,
  seed: number,
  contextIndex: number,
  count: number,
  parent?: string,
) {
  const context = `context-${contextIndex}`;
  const ids: string[] = [];
  for (let index = 0; index < count; index += 1) {
    const id = `s-${seed}-${contextIndex}-${index}`;
    const subgroup = Math.floor(index / Math.max(4, Math.ceil(count / 4)));
    addSpecification(
      fixture,
      id,
      `${vocabulary(seed, contextIndex, 0)} ${vocabulary(seed, contextIndex, 1)} ` +
        `sub${seed}x${contextIndex}q${subgroup} unique${seed}x${contextIndex}q${index}`,
      {kind: "context", context, parent},
    );
    ids.push(id);
  }
  addTerm(fixture, `term-${seed}-${contextIndex}-all`, ids);
  for (let subgroup = 0; subgroup < 4; subgroup += 1) {
    const members = ids.filter(
      (_, index) =>
        Math.floor(index / Math.max(4, Math.ceil(count / 4))) === subgroup,
    );
    if (members.length > 1) {
      addTerm(fixture, `term-${seed}-${contextIndex}-sub-${subgroup}`, members);
    }
  }
  for (let index = 0; index < ids.length; index += 1) {
    addSemantic(
      fixture,
      `semantic-${seed}-${contextIndex}-ring-${index}`,
      ids[index],
      ids[(index + 1) % ids.length],
    );
    addSemantic(
      fixture,
      `semantic-${seed}-${contextIndex}-chord-${index}`,
      ids[index],
      ids[(index + 5 + (index % 7)) % ids.length],
    );
  }
  return {context, ids};
}

function finish(
  id: string,
  seed: number,
  fixture: FixtureBuilder,
  contextIds: string[],
): LayoutFixture {
  return {
    id,
    seed,
    ...fixture,
    contextIds,
  };
}

export function cleanContextFixture(
  seed: number,
  sizes: readonly number[] = [36, 52, 68, 84, 100],
  includeGlobalTerm = true,
): LayoutFixture {
  const fixture = builder();
  const contexts = sizes.map((count, index) =>
    addContext(fixture, seed, index, count),
  );
  if (includeGlobalTerm) {
    addTerm(fixture, `term-${seed}-global`, fixture.specificationIds);
  }
  return finish(
    `clean-${sizes.join("-")}-${includeGlobalTerm ? "global" : "local"}`,
    seed,
    fixture,
    contexts.map((value) => value.context),
  );
}

export function scaleContextFixture(seed: number, count: number): LayoutFixture {
  const proportions = [0.12, 0.16, 0.2, 0.24];
  const sizes = proportions.map((fraction) => Math.floor(count * fraction));
  sizes.push(count - sizes.reduce((sum, size) => sum + size, 0));
  return cleanContextFixture(seed, sizes);
}

export function hierarchicalFixture(seed: number): LayoutFixture {
  const fixture = builder();
  const contextIds: string[] = [];
  for (let parentIndex = 0; parentIndex < 3; parentIndex += 1) {
    const parent = `parent-${parentIndex}`;
    const parentMembers: string[] = [];
    for (let child = 0; child < 3; child += 1) {
      const contextIndex = parentIndex * 3 + child;
      const context = addContext(fixture, seed, contextIndex, 32, parent);
      contextIds.push(context.context);
      parentMembers.push(...context.ids);
    }
    addTerm(fixture, `term-${seed}-${parent}`, parentMembers);
  }
  addTerm(fixture, `term-${seed}-global`, fixture.specificationIds);
  return finish("hierarchical", seed, fixture, contextIds);
}

export function overlapAndBridgeFixture(seed: number): LayoutFixture {
  const fixture = builder();
  const random = deterministicRandom(seed ^ 0xa51ce);
  const contexts = [0, 1, 2].map((index) =>
    addContext(fixture, seed, index, 60),
  );
  const overlapIds: string[] = [];
  for (let index = 0; index < 20; index += 1) {
    const id = `overlap-${seed}-${index}`;
    addSpecification(
      fixture,
      id,
      `${vocabulary(seed, 0, 0)} ${vocabulary(seed, 1, 0)} overlap${seed}q${index}`,
      {kind: "overlap", contexts: [contexts[0].context, contexts[1].context]},
    );
    overlapIds.push(id);
    addSemantic(
      fixture,
      `overlap-left-${index}`,
      id,
      random.pick(contexts[0].ids),
    );
    addSemantic(
      fixture,
      `overlap-right-${index}`,
      id,
      random.pick(contexts[1].ids),
    );
  }
  addTerm(fixture, `term-${seed}-overlap-left`, [
    ...overlapIds,
    ...contexts[0].ids.slice(0, 20),
  ]);
  addTerm(fixture, `term-${seed}-overlap-right`, [
    ...overlapIds,
    ...contexts[1].ids.slice(0, 20),
  ]);

  for (let index = 0; index < 12; index += 1) {
    const id = `bridge-${seed}-${index}`;
    addSpecification(
      fixture,
      id,
      `bridge${seed}q${index} neutral${seed}q${index}`,
      {kind: "bridge", contexts: [contexts[1].context, contexts[2].context]},
    );
    addSemantic(
      fixture,
      `bridge-left-${index}`,
      id,
      contexts[1].ids[Math.floor((index * contexts[1].ids.length) / 12)],
    );
    addSemantic(
      fixture,
      `bridge-right-${index}`,
      id,
      contexts[2].ids[Math.floor((index * contexts[2].ids.length) / 12)],
    );
  }
  addTerm(fixture, `term-${seed}-global`, fixture.specificationIds);
  return finish(
    "overlap-bridge",
    seed,
    fixture,
    contexts.map((value) => value.context),
  );
}

export function noisyIncompleteFixture(seed: number): LayoutFixture {
  const fixture = cleanContextFixture(seed, [48, 56, 64, 72, 80]);
  const random = deterministicRandom(seed ^ 0xbadc0de);
  const retained = fixture.edges.filter(
    (edge) =>
      edge.family === "semantic" ||
      edge.target.endsWith("-global") ||
      random.next() >= 0.3,
  );
  const contextMembers = new Map<string, string[]>();
  for (const id of fixture.specificationIds) {
    const role = fixture.roles.get(id);
    if (role?.kind !== "context") continue;
    const members = contextMembers.get(role.context) ?? [];
    members.push(id);
    contextMembers.set(role.context, members);
  }
  const crossLinkCount = Math.floor(fixture.specificationIds.length * 0.1);
  for (let index = 0; index < crossLinkCount; index += 1) {
    const leftContext = random.pick(fixture.contextIds);
    const rightContext = random.pick(
      fixture.contextIds.filter((value) => value !== leftContext),
    );
    retained.push({
      id: `noise-${seed}-${index}`,
      source: random.pick(contextMembers.get(leftContext) ?? []),
      target: random.pick(contextMembers.get(rightContext) ?? []),
      current: true,
      family: "semantic",
    });
  }
  return {...fixture, id: "noisy-incomplete", edges: retained};
}

export function disconnectedFixture(seed: number): LayoutFixture {
  const fixture = builder();
  const contexts = [30, 55, 85].map((count, index) =>
    addContext(fixture, seed, index, count),
  );
  return finish(
    "disconnected",
    seed,
    fixture,
    contexts.map((value) => value.context),
  );
}

export function nullFixture(seed: number, count = 300): LayoutFixture {
  const fixture = builder();
  for (let index = 0; index < count; index += 1) {
    addSpecification(
      fixture,
      `null-${seed}-${index}`,
      `unique${seed}z${index}`,
      {kind: "unlabeled"},
    );
  }
  addTerm(fixture, `term-${seed}-global`, fixture.specificationIds);
  return finish("null-global-only", seed, fixture, []);
}
