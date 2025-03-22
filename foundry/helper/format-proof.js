const fs = require("fs");

function toHexByteString(bytes) {
  return 'hex"' + Buffer.from(bytes).toString("hex") + '"';
}

function toUint256Array(instances) {
  const flat = instances.flat();
  return (
    `uint256[] memory inputs = new uint256[](${flat.length});\n` +
    flat
      .map((val, i) => {
        const clean = val.startsWith("0x") ? val : "0x" + val;
        return `inputs[${i}] = ${clean};`;
      })
      .join("\n")
  );
}

function main() {
  const raw = fs.readFileSync("zkml/proof.json", "utf8");
  const json = JSON.parse(raw);

  const proof = json.proof;
  const instances = json.instances;

  if (!proof || !instances) {
    throw new Error("Invalid proof.json");
  }

  console.log("\n// === Formatted calldata ===");
  console.log("\nbytes memory proof = " + toHexByteString(proof) + ";");
  console.log(toUint256Array(instances));
}

main();
