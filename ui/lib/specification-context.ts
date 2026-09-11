import type {SpecificationLayoutInputEdge} from "./specification-layout";
import type {GraphNode, ScoreContribution} from "./types";

const SUPPORT_CONTRIBUTION_KINDS = new Set([
  "structural_support",
  "realization_support",
]);

export type SupportContextLink = {
  id: string;
  source: string;
  target: string;
  kind: "structural_support" | "realization_support";
  points: number;
  edgeId: string;
};

export type SupportContext = {
  id: string;
  anchorIds: string[];
  anchorStatement: string;
  memberIds: string[];
  linkIds: string[];
  totalPoints: number;
};

export type SupportContextModel = {
  contexts: SupportContext[];
  links: SupportContextLink[];
  membership: ReadonlyMap<string, readonly string[]>;
  contextualizedNodeCount: number;
  sharedFoundationCount: number;
};

export type ContextPoint = {x: number; y: number};

export type SupportContextBoundary = {
  contextId: string;
  points: ContextPoint[];
};

function supportKind(
  contribution: ScoreContribution,
): SupportContextLink["kind"] | null {
  return SUPPORT_CONTRIBUTION_KINDS.has(contribution.kind)
    ? (contribution.kind as SupportContextLink["kind"])
    : null;
}

function supportLinkId(
  target: string,
  contribution: ScoreContribution,
  ordinal: number,
) {
  return [
    "support-context",
    contribution.kind,
    contribution.sourceNodeId ?? "",
    target,
    contribution.edgeId,
    String(ordinal),
  ].join("\u0000");
}

/**
 * Derive directed positive support links from the current SelectionView.
 *
 * Evidence and conflict contributions affect fitness but do not assert that one
 * Specification stands on another. Only structural and realization support
 * therefore establish context membership.
 */
export function deriveSupportContextLinks(
  nodes: readonly GraphNode[],
): SupportContextLink[] {
  const currentSpecifications = new Map(
    nodes
      .filter(
        (node) =>
          node.nodeKind === "specification" &&
          node.current &&
          node.evaluationState !== "receded",
      )
      .map((node) => [node.id, node]),
  );
  const links: SupportContextLink[] = [];
  const identities = new Set<string>();

  for (const target of currentSpecifications.values()) {
    for (let ordinal = 0; ordinal < target.contributions.length; ordinal += 1) {
      const contribution = target.contributions[ordinal];
      const kind = supportKind(contribution);
      const source = contribution.sourceNodeId;
      if (
        !kind ||
        contribution.points <= 0 ||
        !source ||
        source === target.id ||
        !currentSpecifications.has(source)
      ) {
        continue;
      }
      const identity = [
        kind,
        source,
        target.id,
        contribution.edgeId,
        String(contribution.points),
      ].join("\u0000");
      if (identities.has(identity)) continue;
      identities.add(identity);
      links.push({
        id: supportLinkId(target.id, contribution, ordinal),
        source,
        target: target.id,
        kind,
        points: contribution.points,
        edgeId: contribution.edgeId,
      });
    }
  }

  return links.sort(
    (left, right) =>
      left.source.localeCompare(right.source) ||
      left.target.localeCompare(right.target) ||
      left.kind.localeCompare(right.kind) ||
      left.edgeId.localeCompare(right.edgeId) ||
      left.id.localeCompare(right.id),
  );
}

type StronglyConnectedComponents = {
  components: string[][];
  componentByNode: ReadonlyMap<string, number>;
};

function stronglyConnectedComponents(
  nodeIds: readonly string[],
  outgoing: ReadonlyMap<string, ReadonlySet<string>>,
): StronglyConnectedComponents {
  let nextIndex = 0;
  const indexByNode = new Map<string, number>();
  const lowlinkByNode = new Map<string, number>();
  const stack: string[] = [];
  const onStack = new Set<string>();
  const components: string[][] = [];

  const visit = (nodeId: string) => {
    indexByNode.set(nodeId, nextIndex);
    lowlinkByNode.set(nodeId, nextIndex);
    nextIndex += 1;
    stack.push(nodeId);
    onStack.add(nodeId);

    const targets = [...(outgoing.get(nodeId) ?? [])].sort();
    for (const target of targets) {
      if (!indexByNode.has(target)) {
        visit(target);
        lowlinkByNode.set(
          nodeId,
          Math.min(
            lowlinkByNode.get(nodeId) ?? 0,
            lowlinkByNode.get(target) ?? 0,
          ),
        );
      } else if (onStack.has(target)) {
        lowlinkByNode.set(
          nodeId,
          Math.min(
            lowlinkByNode.get(nodeId) ?? 0,
            indexByNode.get(target) ?? 0,
          ),
        );
      }
    }

    if (lowlinkByNode.get(nodeId) !== indexByNode.get(nodeId)) return;
    const component: string[] = [];
    while (stack.length > 0) {
      const member = stack.pop();
      if (!member) break;
      onStack.delete(member);
      component.push(member);
      if (member === nodeId) break;
    }
    components.push(component.sort());
  };

  for (const nodeId of [...nodeIds].sort()) {
    if (!indexByNode.has(nodeId)) visit(nodeId);
  }

  components.sort((left, right) => left[0].localeCompare(right[0]));
  return {
    components,
    componentByNode: new Map(
      components.flatMap((component, componentIndex) =>
        component.map((nodeId) => [nodeId, componentIndex] as const),
      ),
    ),
  };
}

/**
 * A support context is a directed support basin: a sink SCC is its anchor and
 * every current Specification that can support that anchor is a member.
 *
 * Condensing cycles first makes the result total and deterministic. A shared
 * foundation may reach more than one sink and intentionally belongs to more
 * than one (overlapping) context.
 */
export function deriveSupportContexts(
  nodes: readonly GraphNode[],
): SupportContextModel {
  const links = deriveSupportContextLinks(nodes);
  if (links.length === 0) {
    return {
      contexts: [],
      links,
      membership: new Map(),
      contextualizedNodeCount: 0,
      sharedFoundationCount: 0,
    };
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const involvedNodeIds = [
    ...new Set(links.flatMap((link) => [link.source, link.target])),
  ].sort();
  const outgoing = new Map<string, Set<string>>();
  for (const nodeId of involvedNodeIds) outgoing.set(nodeId, new Set());
  for (const link of links) outgoing.get(link.source)?.add(link.target);

  const {components, componentByNode} = stronglyConnectedComponents(
    involvedNodeIds,
    outgoing,
  );
  const componentOutgoing = components.map(() => new Set<number>());
  const componentIncoming = components.map(() => new Set<number>());
  for (const link of links) {
    const source = componentByNode.get(link.source);
    const target = componentByNode.get(link.target);
    if (source === undefined || target === undefined || source === target) continue;
    componentOutgoing[source].add(target);
    componentIncoming[target].add(source);
  }

  const contexts: SupportContext[] = [];
  for (let sink = 0; sink < components.length; sink += 1) {
    if (componentOutgoing[sink].size > 0) continue;
    const reached = new Set<number>([sink]);
    const pending = [sink];
    while (pending.length > 0) {
      const component = pending.pop();
      if (component === undefined) break;
      for (const predecessor of componentIncoming[component]) {
        if (reached.has(predecessor)) continue;
        reached.add(predecessor);
        pending.push(predecessor);
      }
    }
    const memberIds = [...reached]
      .flatMap((component) => components[component])
      .sort();
    if (memberIds.length < 2) continue;
    const members = new Set(memberIds);
    const contextLinks = links.filter(
      (link) => members.has(link.source) && members.has(link.target),
    );
    const anchorIds = [...components[sink]].sort();
    const anchorStatement =
      anchorIds
        .map((id) => nodeById.get(id)?.statement.trim())
        .find((statement) => statement) ?? anchorIds[0];
    contexts.push({
      id: `support-context:${anchorIds.join("|")}`,
      anchorIds,
      anchorStatement,
      memberIds,
      linkIds: contextLinks.map((link) => link.id),
      totalPoints: contextLinks.reduce((sum, link) => sum + link.points, 0),
    });
  }
  contexts.sort((left, right) => left.id.localeCompare(right.id));

  const membership = new Map<string, string[]>();
  for (const context of contexts) {
    for (const memberId of context.memberIds) {
      const memberships = membership.get(memberId) ?? [];
      memberships.push(context.id);
      membership.set(memberId, memberships);
    }
  }
  for (const memberships of membership.values()) memberships.sort();

  return {
    contexts,
    links,
    membership,
    contextualizedNodeCount: membership.size,
    sharedFoundationCount: [...membership.values()].filter(
      (memberships) => memberships.length > 1,
    ).length,
  };
}

/** Invisible, factual layout inputs for support contributions shown as basins. */
export function supportContextLayoutEdges(
  model: SupportContextModel,
): SpecificationLayoutInputEdge[] {
  return model.links.map((link) => ({
    id: link.id,
    source: link.source,
    target: link.target,
    current: true,
    family: "selection",
  }));
}

function convexHull(points: readonly ContextPoint[]): ContextPoint[] {
  const unique = [
    ...new Map(
      points.map((point) => [`${point.x}\u0000${point.y}`, point] as const),
    ).values(),
  ].sort((left, right) => left.x - right.x || left.y - right.y);
  if (unique.length <= 2) return unique;
  const cross = (origin: ContextPoint, left: ContextPoint, right: ContextPoint) =>
    (left.x - origin.x) * (right.y - origin.y) -
    (left.y - origin.y) * (right.x - origin.x);
  const lower: ContextPoint[] = [];
  for (const point of unique) {
    while (
      lower.length >= 2 &&
      cross(lower[lower.length - 2], lower[lower.length - 1], point) <= 0
    ) {
      lower.pop();
    }
    lower.push(point);
  }
  const upper: ContextPoint[] = [];
  for (let index = unique.length - 1; index >= 0; index -= 1) {
    const point = unique[index];
    while (
      upper.length >= 2 &&
      cross(upper[upper.length - 2], upper[upper.length - 1], point) <= 0
    ) {
      upper.pop();
    }
    upper.push(point);
  }
  lower.pop();
  upper.pop();
  return [...lower, ...upper];
}

function capsule(
  left: ContextPoint,
  right: ContextPoint,
  padding: number,
): ContextPoint[] {
  const center = {x: (left.x + right.x) / 2, y: (left.y + right.y) / 2};
  const dx = right.x - left.x;
  const dy = right.y - left.y;
  const distance = Math.max(0.001, Math.hypot(dx, dy));
  const ux = dx / distance;
  const uy = dy / distance;
  const nx = -uy;
  const ny = ux;
  const major = distance / 2 + padding;
  const minor = padding;
  return Array.from({length: 24}, (_, index) => {
    const angle = (index / 24) * Math.PI * 2;
    const along = Math.cos(angle) * major;
    const across = Math.sin(angle) * minor;
    return {
      x: center.x + ux * along + nx * across,
      y: center.y + uy * along + ny * across,
    };
  });
}

function smoothClosedPolygon(points: readonly ContextPoint[]) {
  const smoothed: ContextPoint[] = [];
  for (let index = 0; index < points.length; index += 1) {
    const current = points[index];
    const next = points[(index + 1) % points.length];
    smoothed.push(
      current,
      {
        x: (current.x + next.x) / 2,
        y: (current.y + next.y) / 2,
      },
    );
  }
  return smoothed;
}

/**
 * Build inexpensive closed XY boundaries around the currently positioned
 * members. The envelope follows declared membership rather than density; an
 * unrelated point can geometrically overlap it without acquiring membership.
 */
export function buildSupportContextBoundaries(
  contexts: readonly SupportContext[],
  positions: ReadonlyMap<string, ContextPoint>,
  padding = 10,
): SupportContextBoundary[] {
  const boundaries: SupportContextBoundary[] = [];
  for (const context of contexts) {
    const memberPoints = context.memberIds.flatMap((memberId) => {
      const point = positions.get(memberId);
      return point ? [point] : [];
    });
    if (memberPoints.length < 2) continue;
    const hull = convexHull(memberPoints);
    if (hull.length < 2) continue;
    if (hull.length === 2) {
      boundaries.push({
        contextId: context.id,
        points: capsule(hull[0], hull[1], padding),
      });
      continue;
    }
    const center = {
      x: hull.reduce((sum, point) => sum + point.x, 0) / hull.length,
      y: hull.reduce((sum, point) => sum + point.y, 0) / hull.length,
    };
    const expanded = hull.map((point) => {
      const dx = point.x - center.x;
      const dy = point.y - center.y;
      const distance = Math.max(0.001, Math.hypot(dx, dy));
      return {
        x: point.x + (dx / distance) * padding,
        y: point.y + (dy / distance) * padding,
      };
    });
    boundaries.push({
      contextId: context.id,
      points: smoothClosedPolygon(expanded),
    });
  }
  return boundaries;
}
