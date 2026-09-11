import type {GraphNode} from "../lib/types";
import type {SpecificationProximityModel} from "../lib/specification-proximity";
import type {SparseAffinityModel} from "./affinity";
import {densityBasinMemberships, nearestNeighbors} from "./metrics";
import type {LayoutCoordinates} from "./types";

function featureLabel(
  id: string,
  nodesById: ReadonlyMap<string, GraphNode>,
) {
  const connectorId = id.replace(/^(shared_term|shared_projection):/, "");
  return (
    nodesById.get(connectorId)?.statement ??
    id
      .replace(/^(lexical_unigram|lexical_bigram):/, "")
      .split("\u0001")
      .join(" ")
  );
}

/**
 * Read coordinate-derived density regions back to the source graph. This is
 * deliberately offline: memberships never feed the candidate layout or the
 * renderer and therefore cannot become a hidden second placement phase.
 */
export function diagnoseSpatialLandscape(
  model: SparseAffinityModel,
  proximity: SpecificationProximityModel,
  coordinates: LayoutCoordinates,
  nodesById: ReadonlyMap<string, GraphNode>,
  scales: readonly number[] = [10, 20, 40],
) {
  const ids = model.specificationNodes.map((node) => node.id);
  const features = proximity.hyperedges.map((feature) => ({
    ...feature,
    indexes: feature.members.flatMap((member) => {
      const index = model.specificationIndex.get(member.specificationId);
      return index === undefined ? [] : [index];
    }),
  }));

  return densityBasinMemberships(ids, coordinates, scales).map(
    ({scale, basins, coveredFraction}) => ({
      scale,
      coveredFraction,
      basinCount: basins.length,
      basins: basins
        .map((members, basinIndex) => {
          const membership = new Set(members);
          let internalWeight = 0;
          let boundaryWeight = 0;
          for (const edge of model.edges) {
            const sourceInside = membership.has(edge.source);
            const targetInside = membership.has(edge.target);
            if (sourceInside && targetInside) internalWeight += edge.rawWeight;
            else if (sourceInside !== targetInside) boundaryWeight += edge.rawWeight;
          }
          const featureExplanations = features
            .map((feature) => {
              let overlap = 0;
              for (const index of feature.indexes) {
                if (membership.has(index)) overlap += 1;
              }
              const expected =
                (feature.degree * members.length) /
                Math.max(1, model.specificationNodes.length);
              const basinShare = overlap / Math.max(1, members.length);
              const corpusShare =
                feature.degree / Math.max(1, model.specificationNodes.length);
              const lift = corpusShare > 0 ? basinShare / corpusShare : 0;
              const excess = overlap - expected;
              return {
                signal: feature.signal,
                feature: featureLabel(feature.id, nodesById),
                overlap,
                corpusDegree: feature.degree,
                basinShare,
                lift,
                excess,
                score: excess > 0 ? excess * Math.log2(1 + lift) : 0,
              };
            })
            .filter((feature) => feature.overlap >= 2 && feature.score > 0)
            .sort(
              (left, right) =>
                right.score - left.score ||
                right.overlap - left.overlap ||
                left.corpusDegree - right.corpusDegree ||
                left.feature.localeCompare(right.feature),
            )
            .slice(0, 12)
            .map(({score: _score, ...feature}) => feature);
          const representatives = members
            .map((index) => {
              const id = ids[index];
              const radius =
                nearestNeighbors(id, ids, coordinates, scale).at(-1)?.distance ??
                Number.POSITIVE_INFINITY;
              return {
                id,
                localRadius: radius,
                statement: model.specificationNodes[index].statement,
              };
            })
            .sort(
              (left, right) =>
                left.localRadius - right.localRadius ||
                left.id.localeCompare(right.id),
            )
            .slice(0, 6);
          return {
            basin: basinIndex,
            size: members.length,
            sourceAffinity: {
              internalWeight,
              boundaryWeight,
              internalShare:
                internalWeight + boundaryWeight > 0
                  ? internalWeight / (internalWeight + boundaryWeight)
                  : 0,
            },
            representatives,
            featureExplanations,
          };
        })
        .sort(
          (left, right) =>
            right.size - left.size ||
            right.sourceAffinity.internalShare -
              left.sourceAffinity.internalShare,
        ),
    }),
  );
}
