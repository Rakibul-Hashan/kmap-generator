
    // --- Main Setup & Event Listeners ---
    const solveBtn = document.getElementById("solve-btn");
    const autoSolveCheck = document.getElementById("auto-solve-check");
    const inputs = [
      document.getElementById("term-input"),
      document.getElementById("dont-care-input"),
      document.getElementById("variable-select"),
      document.getElementById("term-type-select")
    ];
    solveBtn.addEventListener("click", solveKmap);
    inputs.forEach(input => input.addEventListener('input', () => {
      if (autoSolveCheck.checked) {
        debouncedSolve();
      }
    }));
    let debounceTimer;
    const debouncedSolve = () => {
      clearTimeout(debounceTimer);
      debounceTimer = setTimeout(solveKmap, 300);
    };
    // --- Core Solver Logic ---
    function solveKmap() {
      const solutionDiv = document.getElementById("solution");
      const errorDiv = document.getElementById("error-message");
      solutionDiv.innerHTML = "";
      errorDiv.innerHTML = "";
      try {
        const {
          requiredTerms,
          dontCares,
          numVars,
          termType
        } = parseAndValidateInputs();
        let termsToGroup, termsToCover;
        if (termType === 'min') { // SoP
          termsToGroup = [...new Set([...requiredTerms, ...dontCares])]; // Group 1s and Xs
          termsToCover = requiredTerms; // But only need to cover the 1s
        } else { // PoS
          const maxTerm = Math.pow(2, numVars) - 1;
          const allTerms = Array.from({
            length: maxTerm + 1
          }, (_, i) => i);
          const maxTermSet = new Set(requiredTerms);
          const zeroTerms = allTerms.filter(t => !maxTermSet.has(t));
          termsToGroup = [...new Set([...zeroTerms, ...dontCares])]; // Group 0s and Xs
          termsToCover = zeroTerms; // But only need to cover the 0s
        }
        const primeImplicants = findPrimeImplicants(termsToGroup, numVars);
        const essentialGroups = selectEssentialImplicants(primeImplicants, termsToCover);
        const simplifyFn = termType === 'min' ? simplifyGroupSoP : simplifyGroupPoS;
        const simplifiedTerms = essentialGroups.map(group => simplifyFn(group, numVars));
        renderSolution(requiredTerms, dontCares, numVars, essentialGroups, simplifiedTerms, termType);
      } catch (error) {
        errorDiv.innerText = error.message;
      }
    }

    function parseAndValidateInputs() {
      const requiredStr = document.getElementById("term-input").value;
      const dontCareStr = document.getElementById("dont-care-input").value;
      const numVars = parseInt(document.getElementById("variable-select").value);
      const termType = document.getElementById("term-type-select").value;
      const parse = str => str.split(/[\s,]+/).filter(s => s.trim() !== "").map(Number);
      const requiredTerms = parse(requiredStr);
      const dontCares = parse(dontCareStr);
      if (requiredTerms.some(isNaN) || dontCares.some(isNaN)) {
        throw new Error("Input contains non-numeric values.");
      }
      const maxTerm = Math.pow(2, numVars) - 1;
      const allTerms = [...requiredTerms, ...dontCares];
      if (allTerms.some(t => t > maxTerm)) {
        throw new Error(`Terms cannot be greater than ${maxTerm} for ${numVars} variables.`);
      }
      const termCounts = {};
      allTerms.forEach(t => termCounts[t] = (termCounts[t] || 0) + 1);
      if (Object.values(termCounts).some(count => count > 1)) {
        throw new Error("The same term cannot be in both required and don't care lists.");
      }
      return {
        requiredTerms: [...new Set(requiredTerms)].sort((a, b) => a - b),
        dontCares: [...new Set(dontCares)].sort((a, b) => a - b),
        numVars,
        termType
      };
    }

    function findPrimeImplicants(terms, numVars) {
      if (terms.length === 0) return [];
      let groups = terms.map(m => [m]);
      const primeImplicants = [];
      while (groups.length > 0) {
        const usedInNextLevel = new Set();
        const nextGroupsMap = new Map();
        let madeCombination = false;
        for (let i = 0; i < groups.length; i++) {
          for (let j = i + 1; j < groups.length; j++) {
            const g1 = groups[i],
              g2 = groups[j];
            if (g1.length !== g2.length) continue;
            const diff = g1.map((val, idx) => val ^ g2[idx]);
            const firstDiff = diff[0];
            const isPowerOfTwo = firstDiff > 0 && (firstDiff & (firstDiff - 1)) === 0;
            if (diff.every(d => d === firstDiff) && isPowerOfTwo) {
              madeCombination = true;
              usedInNextLevel.add(JSON.stringify(g1));
              usedInNextLevel.add(JSON.stringify(g2));
              const combined = [...new Set([...g1, ...g2])].sort((a, b) => a - b);
              nextGroupsMap.set(JSON.stringify(combined), combined);
            }
          }
        }
        groups.forEach(g => {
          if (!usedInNextLevel.has(JSON.stringify(g))) primeImplicants.push(g);
        });
        if (!madeCombination) break;
        groups = Array.from(nextGroupsMap.values());
      }
      return Array.from(new Set(primeImplicants.map(JSON.stringify)), JSON.parse);
    }

    function selectEssentialImplicants(primeImplicants, termsToCover) {
      if (termsToCover.length === 0) return [];
      const coverage = new Map(termsToCover.map(m => [m, []]));
      primeImplicants.forEach((group, i) => {
        group.forEach(m => {
          if (coverage.has(m)) coverage.get(m).push(i);
        });
      });
      const essentialPIIndices = new Set();
      const coveredTerms = new Set();
      coverage.forEach((piIndices, term) => {
        if (piIndices.length === 1) {
          const piIndex = piIndices[0];
          essentialPIIndices.add(piIndex);
          primeImplicants[piIndex].forEach(t => {
            if (termsToCover.includes(t)) coveredTerms.add(t);
          });
        }
      });
      let essentialGroups = Array.from(essentialPIIndices).map(i => primeImplicants[i]);
      let uncoveredTerms = termsToCover.filter(t => !coveredTerms.has(t));
      let remainingPIs = primeImplicants.filter((_, i) => !essentialPIIndices.has(i));
      while (uncoveredTerms.length > 0) {
        if (remainingPIs.length === 0) break;
        remainingPIs.sort((a, b) => {
          const coverA = a.filter(t => uncoveredTerms.includes(t)).length;
          const coverB = b.filter(t => uncoveredTerms.includes(t)).length;
          return (coverB - coverA) || (a.length - b.length);
        });
        const bestPI = remainingPIs.shift();
        if (bestPI) {
          essentialGroups.push(bestPI);
          bestPI.forEach(t => {
            const index = uncoveredTerms.indexOf(t);
            if (index > -1) uncoveredTerms.splice(index, 1);
          });
        }
      }
      return essentialGroups;
    }

    function decToBin(dec, len) {
      return (dec >>> 0).toString(2).padStart(len, "0");
    }

    function simplifyGroupSoP(group, numVars) {
      if (group.length === 0) return "";
      if (group.length === Math.pow(2, numVars)) return "1";
      const variables = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(0, numVars);
      const binaryReps = group.map(m => decToBin(m, numVars));
      let term = "";
      for (let i = 0; i < numVars; i++) {
        const firstBit = binaryReps[0][i];
        if (binaryReps.every(bin => bin[i] === firstBit)) {
          term += variables[i];
          if (firstBit === "0") term += "'";
        }
      }
      return term;
    }

    function simplifyGroupPoS(group, numVars) {
      if (group.length === 0) return "";
      if (group.length === Math.pow(2, numVars)) return "0";
      const variables = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".slice(0, numVars);
      const binaryReps = group.map(m => decToBin(m, numVars));
      let term = [];
      for (let i = 0; i < numVars; i++) {
        const firstBit = binaryReps[0][i];
        if (binaryReps.every(bin => bin[i] === firstBit)) {
          let literal = variables[i];
          if (firstBit === '1') literal += "'";
          term.push(literal);
        }
      }
      return `(${term.join(" + ")})`;
    }
    // --- Rendering Logic ---
    function renderSolution(requiredTerms, dontCares, numVars, groups, terms, termType) {
      const solutionDiv = document.getElementById("solution");
      const colors = ["#f87171", "#fb923c", "#fbbf24", "#a3e635", "#4ade80", "#34d399", "#22d3ee", "#60a5fa", "#818cf8", "#a78bfa", "#f472b6", "#fb7185"];
      const operator = termType === 'min' ? ' + ' : '';
      let finalExpression = terms.join(operator) || (termType === 'min' ? '0' : '1');
      let finalHtml = `
            <div class="solution-step">
                <h2>Final Simplified Expression</h2>
                <div class="final-expression">F = ${finalExpression}</div>
            </div>`;
      finalHtml += `
            <div class="solution-step">
                <h2>Complete K-Map with Groupings</h2>
                ${renderKMap(requiredTerms, dontCares, numVars, groups, colors)}
            </div>`;
      groups.forEach((group, index) => {
        finalHtml += `
                <div class="solution-step">
                    <h2>Group ${index + 1}: ${group.length}-Cell Grouping (${group.join(",")})</h2>
                    <p class="final-expression">Simplified Term: ${terms[index]}</p>
                    ${renderKMap(requiredTerms, dontCares, numVars, [group], [colors[index % colors.length]])}
                </div>`;
      });
      solutionDiv.innerHTML = finalHtml;
    }

    function getKMapLayout(numVars) {
      if (numVars <= 2) {
        const rowVars = ["A"],
          colVars = ["B"];
        const rows = ["0", "1"],
          cols = ["0", "1"];
        const getMinterm = (mapIdx, r, c) => parseInt(rows[r] + cols[c], 2);
        return {
          rowVars,
          colVars,
          rows,
          cols,
          getMinterm,
          mapCount: 1
        };
      }
      if (numVars === 3) {
        const rowVars = ["A"],
          colVars = ["B", "C"];
        const rows = ["0", "1"],
          cols = ["00", "01", "11", "10"];
        const getMinterm = (mapIdx, r, c) => parseInt(rows[r] + cols[c], 2);
        return {
          rowVars,
          colVars,
          rows,
          cols,
          getMinterm,
          mapCount: 1
        };
      }
      if (numVars === 4) {
        const rowVars = ["A", "B"],
          colVars = ["C", "D"];
        const rows = ["00", "01", "11", "10"],
          cols = ["00", "01", "11", "10"];
        const getMinterm = (mapIdx, r, c) => parseInt(rows[r] + cols[c], 2);
        return {
          rowVars,
          colVars,
          rows,
          cols,
          getMinterm,
          mapCount: 1
        };
      }
      if (numVars === 5) {
        const rowVars = ["B", "C"],
          colVars = ["D", "E"];
        const rows = ["00", "01", "11", "10"],
          cols = ["00", "01", "11", "10"];
        const getMinterm = (mapIdx, r, c) => parseInt(mapIdx.toString() + rows[r] + cols[c], 2);
        return {
          rowVars,
          colVars,
          rows,
          cols,
          getMinterm,
          mapCount: 2
        };
      }
    }

    function renderKMap(requiredTerms, dontCares, numVars, groupsToHighlight = [], colors = []) {
      const layout = getKMapLayout(numVars);
      const requiredSet = new Set(requiredTerms);
      const dontCareSet = new Set(dontCares);
      let html = '<div class="kmap-container">';
      for (let mapIdx = 0; mapIdx < layout.mapCount; mapIdx++) {
        if (layout.mapCount > 1) html += `<div><h3>${numVars === 5 ? "A" : "V"}=${mapIdx}</h3>`;
        html += '<table class="kmap-table">';
        html += `<tr><th>${layout.rowVars.join("")}\\${layout.colVars.join("")}</th>`;
        layout.cols.forEach(c => html += `<th>${c}</th>`);
        html += "</tr>";
        layout.rows.forEach((r, rIdx) => {
          html += `<tr><th>${r}</th>`;
          layout.cols.forEach((c, cIdx) => {
            const minterm = layout.getMinterm(mapIdx, rIdx, cIdx);
            let val = "0";
            let valClass = "";
            if (requiredSet.has(minterm)) {
              val = "1";
            } else if (dontCareSet.has(minterm)) {
              val = "X";
              valClass = "dont-care";
            }
            let styles = "";
            groupsToHighlight.forEach((group, gIdx) => {
              if (group.includes(minterm)) {
                styles += `border: 3px solid ${colors[gIdx % colors.length]}; box-shadow: 0 0 10px ${colors[gIdx % colors.length]};`;
              }
            });
            html += `<td style="${styles}">
                                   <span class="minterm-index">${minterm}</span>
                                   <span class="${valClass}">${val}</span>
                               </td>`;
          });
          html += "</tr>";
        });
        html += "</table>";
        if (layout.mapCount > 1) html += `</div>`;
      }
      html += "</div>";
      return html;
    }
  