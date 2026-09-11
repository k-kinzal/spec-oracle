declare module "d3-force-3d" {
  export interface SimulationNodeDatum {
    index?: number;
    x?: number;
    y?: number;
    z?: number;
    vx?: number;
    vy?: number;
    vz?: number;
    fx?: number | null;
    fy?: number | null;
    fz?: number | null;
  }

  export interface SimulationLinkDatum<NodeDatum extends SimulationNodeDatum> {
    source: string | number | NodeDatum;
    target: string | number | NodeDatum;
    index?: number;
  }

  export interface Force<NodeDatum extends SimulationNodeDatum> {
    (alpha: number): void;
  }

  export interface ForceLink<
    NodeDatum extends SimulationNodeDatum,
    LinkDatum extends SimulationLinkDatum<NodeDatum>,
  > extends Force<NodeDatum> {
    id(accessor: (node: NodeDatum) => string): this;
    links(links: LinkDatum[]): this;
    distance(distance: number | ((link: LinkDatum) => number)): this;
    strength(strength: number | ((link: LinkDatum) => number)): this;
  }

  export interface ForceManyBody<NodeDatum extends SimulationNodeDatum>
    extends Force<NodeDatum> {
    strength(strength: number | ((node: NodeDatum) => number)): this;
    theta(theta: number): this;
    distanceMin(distance: number): this;
    distanceMax(distance: number): this;
  }

  export interface ForceCollide<NodeDatum extends SimulationNodeDatum>
    extends Force<NodeDatum> {
    radius(radius: number | ((node: NodeDatum) => number)): this;
    strength(strength: number): this;
  }

  export interface ForceCenter<NodeDatum extends SimulationNodeDatum>
    extends Force<NodeDatum> {
    strength(strength: number): this;
  }

  export interface ForcePosition<NodeDatum extends SimulationNodeDatum>
    extends Force<NodeDatum> {
    strength(strength: number | ((node: NodeDatum) => number)): this;
  }

  export interface Simulation<NodeDatum extends SimulationNodeDatum> {
    stop(): this;
    restart(): this;
    tick(iterations?: number): this;
    nodes(nodes: NodeDatum[]): this;
    alpha(): number;
    alpha(value: number): this;
    alphaMin(value: number): this;
    alphaDecay(value: number): this;
    velocityDecay(value: number): this;
    randomSource(source: () => number): this;
    force(name: string, force: Force<NodeDatum>): this;
    on(type: "tick" | "end", listener: () => void): this;
  }

  export function forceSimulation<NodeDatum extends SimulationNodeDatum>(
    nodes?: NodeDatum[],
    dimensions?: 1 | 2 | 3,
  ): Simulation<NodeDatum>;
  export function forceLink<
    NodeDatum extends SimulationNodeDatum,
    LinkDatum extends SimulationLinkDatum<NodeDatum>,
  >(links?: LinkDatum[]): ForceLink<NodeDatum, LinkDatum>;
  export function forceManyBody<
    NodeDatum extends SimulationNodeDatum,
  >(): ForceManyBody<NodeDatum>;
  export function forceCollide<
    NodeDatum extends SimulationNodeDatum,
  >(): ForceCollide<NodeDatum>;
  export function forceCenter<NodeDatum extends SimulationNodeDatum>(
    x?: number,
    y?: number,
    z?: number,
  ): ForceCenter<NodeDatum>;
  export function forceX<NodeDatum extends SimulationNodeDatum>(
    x?: number | ((node: NodeDatum) => number),
  ): ForcePosition<NodeDatum>;
  export function forceY<NodeDatum extends SimulationNodeDatum>(
    y?: number | ((node: NodeDatum) => number),
  ): ForcePosition<NodeDatum>;
  export function forceZ<NodeDatum extends SimulationNodeDatum>(
    z?: number,
  ): ForcePosition<NodeDatum>;
}
