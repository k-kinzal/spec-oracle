import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "spec-oracle — graph view",
  description:
    "The specification graph in constrained natural language, visualized.",
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
