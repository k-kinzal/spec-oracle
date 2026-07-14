// The gRPC backend-for-frontend seam. This module runs ONLY on the Next.js
// server (Node runtime): it loads the shared spec_oracle.v1 .proto and dials
// specd over HTTP/2. The browser never imports this file — it calls the
// /api/graph Route Handler, which calls in here. This keeps specd gRPC-only and
// mirrors so_client's thin-client role, in TypeScript.

import path from "node:path";
import * as grpc from "@grpc/grpc-js";
import * as protoLoader from "@grpc/proto-loader";

// One source of truth for the wire contract: the same .proto the Rust crates
// compile. Resolved from the UI project root by default (../so_protocol/proto),
// overridable for non-standard layouts.
const PROTO_DIR =
  process.env.SPEC_ORACLE_PROTO_DIR ??
  path.join(process.cwd(), "..", "so_protocol", "proto");
const PROTO_PATH = path.join(
  PROTO_DIR,
  "spec_oracle",
  "v1",
  "specification.proto",
);

// host:port with NO scheme — grpc-js dials it directly.
const GRPC_ADDR = process.env.SPEC_ORACLE_GRPC_ADDR ?? "127.0.0.1:50051";

// The wire page, field names verbatim from the proto (keepCase). `total_nodes`
// is a uint64 rendered as a string (longs: String) to avoid precision loss.
export type WireGraphPage = {
  nodes: unknown[];
  term_nodes: unknown[];
  derived_nodes: unknown[];
  edges: unknown[];
  next_page_token: string;
  total_nodes: string;
};

export type WireLedgerPage = {
  term_nodes: unknown[];
  derived_nodes: unknown[];
  edges: unknown[];
  next_page_token: string;
  total_edges: string;
};

type GraphClient = grpc.Client & {
  GetGraph: (
    req: { page_size: number; page_token: string },
    cb: (err: grpc.ServiceError | null, resp: WireGraphPage) => void,
  ) => void;
  GetLedger: (
    req: { page_size: number; page_token: string },
    cb: (err: grpc.ServiceError | null, resp: WireLedgerPage) => void,
  ) => void;
};

// A single client is reused across requests (a fresh channel per request would
// leak connections). Cached on the module, which the Node runtime keeps warm.
let cached: GraphClient | null = null;

function client(): GraphClient {
  if (cached) return cached;
  const packageDefinition = protoLoader.loadSync(PROTO_PATH, {
    keepCase: true,
    longs: String,
    enums: String,
    defaults: true,
    oneofs: true,
    includeDirs: [PROTO_DIR],
  });
  const proto = grpc.loadPackageDefinition(packageDefinition) as unknown as {
    spec_oracle: {
      v1: {
        SpecificationGraph: new (
          addr: string,
          creds: grpc.ChannelCredentials,
        ) => GraphClient;
      };
    };
  };
  cached = new proto.spec_oracle.v1.SpecificationGraph(
    GRPC_ADDR,
    grpc.credentials.createInsecure(),
  );
  return cached;
}

export function getLedger(
  pageSize: number,
  pageToken: string,
): Promise<WireLedgerPage> {
  return new Promise((resolve, reject) => {
    client().GetLedger(
      { page_size: pageSize, page_token: pageToken },
      (err, resp) => (err ? reject(err) : resolve(resp)),
    );
  });
}

/** Fetch one bounded page of the graph from specd. */
export function getGraph(
  pageSize: number,
  pageToken: string,
): Promise<WireGraphPage> {
  return new Promise((resolve, reject) => {
    client().GetGraph(
      { page_size: pageSize, page_token: pageToken },
      (err, resp) => (err ? reject(err) : resolve(resp)),
    );
  });
}
