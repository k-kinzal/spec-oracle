import type {
  SpecificationLayoutInputEdge,
  SpecificationLayoutInputNode,
  SpecificationLayoutResult,
} from "../lib/specification-layout";
import {
  deriveSpecificationProximity,
  normalizedInverseDocumentFrequency,
} from "../lib/specification-proximity";

function stableHash(value: string) {
  let hash = 2166136261;
  for (let index = 0; index < value.length; index += 1) {
    hash ^= value.charCodeAt(index);
    hash = Math.imul(hash, 16777619);
  }
  return hash >>> 0;
}

function projection(identity: string, channel: string) {
  // Uniform[-sqrt(3), sqrt(3)] has unit variance. Two independent channels
  // make the expected squared distance preserve weighted feature cosine
  // distance without learning a context or a corpus-specific axis.
  return (
    (stableHash(`${channel}\u0000${identity}`) / 4294967296) * 2 - 1
  ) * Math.sqrt(3);
}

export function layoutWithFeatureProjection(
  nodes: SpecificationLayoutInputNode[],
  edges: SpecificationLayoutInputEdge[],
  options: {degreeExponent?: number; informationExponent?: number} = {},
): SpecificationLayoutResult {
  const specifications = nodes.filter(
    (node) => node.nodeKind === "specification",
  );
  const specificationIndex = new Map(
    specifications.map((node, index) => [node.id, index]),
  );
  const proximity = deriveSpecificationProximity(nodes, edges);
  const x = new Float64Array(specifications.length);
  const y = new Float64Array(specifications.length);
  const normSquared = new Float64Array(specifications.length);
  const addFeature = (index: number, identity: string, weight: number) => {
    if (!(weight > 0)) return;
    x[index] += weight * projection(identity, "feature-x");
    y[index] += weight * projection(identity, "feature-y");
    normSquared[index] += weight * weight;
  };

  for (const hyperedge of proximity.hyperedges) {
    const information = normalizedInverseDocumentFrequency(
      specifications.length,
      hyperedge.degree,
    );
    if (information <= 0) continue;
    const degreeScale = Math.pow(
      hyperedge.degree,
      Math.min(0.5, Math.max(0, options.degreeExponent ?? 0.5)),
    );
    const informationScale = Math.pow(
      information,
      Math.max(0, options.informationExponent ?? 1),
    );
    for (const member of hyperedge.members) {
      const index = specificationIndex.get(member.specificationId);
      if (index === undefined) continue;
      addFeature(
        index,
        `${hyperedge.signal}\u0000${hyperedge.id}`,
        member.weight * degreeScale * informationScale,
      );
    }
  }
  for (const link of proximity.links) {
    if (link.signal !== "semantic" && link.signal !== "selection") continue;
    const source = specificationIndex.get(link.source);
    const target = specificationIndex.get(link.target);
    if (source === undefined || target === undefined) continue;
    const weight = link.weight * (link.signal === "selection" ? 1.5 : 1);
    const identity = `${link.signal}\u0000${link.id}`;
    addFeature(source, identity, weight);
    addFeature(target, identity, weight);
  }

  const inactive = specifications
    .map((_, index) => index)
    .filter((index) => normSquared[index] <= 1e-12)
    .sort(
      (left, right) =>
        stableHash(`inactive\u0000${specifications[left].id}`) -
        stableHash(`inactive\u0000${specifications[right].id}`),
    );
  const goldenAngle = Math.PI * (3 - Math.sqrt(5));
  for (let rank = 0; rank < inactive.length; rank += 1) {
    const index = inactive[rank];
    const radius =
      Math.sqrt((rank + 0.5) / Math.max(1, inactive.length)) * 2;
    const angle = rank * goldenAngle;
    x[index] = Math.cos(angle) * radius;
    y[index] = Math.sin(angle) * radius;
    normSquared[index] = 1;
  }
  for (let index = 0; index < specifications.length; index += 1) {
    const norm = Math.sqrt(Math.max(1e-12, normSquared[index]));
    x[index] = (x[index] / norm) * 120;
    y[index] = (y[index] / norm) * 120;
  }

  const incident = new Map<string, number[]>();
  for (const edge of edges) {
    const source = specificationIndex.get(edge.source);
    const target = specificationIndex.get(edge.target);
    if (source !== undefined && target === undefined) {
      const values = incident.get(edge.target) ?? [];
      values.push(source);
      incident.set(edge.target, values);
    } else if (target !== undefined && source === undefined) {
      const values = incident.get(edge.source) ?? [];
      values.push(target);
      incident.set(edge.source, values);
    }
  }
  const positions = new Float32Array(nodes.length * 3);
  for (let index = 0; index < nodes.length; index += 1) {
    const specification = specificationIndex.get(nodes[index].id);
    const members = incident.get(nodes[index].id) ?? [];
    const point =
      specification !== undefined
        ? {x: x[specification], y: y[specification]}
        : members.length > 0
          ? {
              x: members.reduce((sum, member) => sum + x[member], 0) / members.length,
              y: members.reduce((sum, member) => sum + y[member], 0) / members.length,
            }
          : {x: 0, y: 0};
    positions[index * 3] = point.x;
    positions[index * 3 + 1] = point.y;
    positions[index * 3 + 2] = 0;
  }
  return {
    ids: nodes.map((node) => node.id),
    positions,
    featureCount: proximity.featureCount,
    routeCount: proximity.routeCount,
    iterations: 1,
  };
}
