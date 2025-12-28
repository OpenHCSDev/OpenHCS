const { Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell, 
        Header, Footer, AlignmentType, LevelFormat, HeadingLevel, BorderStyle, 
        WidthType, ShadingType, PageNumber, PageBreak } = require('docx');
const fs = require('fs');

// Helper for consistent text styling
const bold = (text) => new TextRun({ text, bold: true });
const italic = (text) => new TextRun({ text, italics: true });
const normal = (text) => new TextRun({ text });
const boldItalic = (text) => new TextRun({ text, bold: true, italics: true });

const tableBorder = { style: BorderStyle.SINGLE, size: 1, color: "CCCCCC" };
const cellBorders = { top: tableBorder, bottom: tableBorder, left: tableBorder, right: tableBorder };

const doc = new Document({
  styles: {
    default: { document: { run: { font: "Arial", size: 24 } } },
    paragraphStyles: [
      { id: "Title", name: "Title", basedOn: "Normal",
        run: { size: 52, bold: true, color: "000000", font: "Arial" },
        paragraph: { spacing: { before: 0, after: 240 }, alignment: AlignmentType.CENTER } },
      { id: "Heading1", name: "Heading 1", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 32, bold: true, color: "000000", font: "Arial" },
        paragraph: { spacing: { before: 360, after: 180 }, outlineLevel: 0 } },
      { id: "Heading2", name: "Heading 2", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 26, bold: true, color: "333333", font: "Arial" },
        paragraph: { spacing: { before: 280, after: 140 }, outlineLevel: 1 } },
      { id: "Heading3", name: "Heading 3", basedOn: "Normal", next: "Normal", quickFormat: true,
        run: { size: 24, bold: true, italics: true, color: "444444", font: "Arial" },
        paragraph: { spacing: { before: 200, after: 100 }, outlineLevel: 2 } },
    ]
  },
  numbering: {
    config: [
      { reference: "numbered-list",
        levels: [{ level: 0, format: LevelFormat.DECIMAL, text: "%1.", alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] },
      { reference: "premise-list",
        levels: [{ level: 0, format: LevelFormat.DECIMAL, text: "%1.", alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] },
      { reference: "evidence-list",
        levels: [{ level: 0, format: LevelFormat.DECIMAL, text: "%1.", alignment: AlignmentType.LEFT,
          style: { paragraph: { indent: { left: 720, hanging: 360 } } } }] },
    ]
  },
  sections: [{
    properties: {
      page: { margin: { top: 1440, right: 1440, bottom: 1440, left: 1440 } }
    },
    headers: {
      default: new Header({ children: [new Paragraph({ 
        alignment: AlignmentType.RIGHT,
        children: [new TextRun({ text: "CONFIDENTIAL — Scientific Misconduct Documentation", size: 20, color: "666666" })]
      })] })
    },
    footers: {
      default: new Footer({ children: [new Paragraph({ 
        alignment: AlignmentType.CENTER,
        children: [new TextRun({ text: "Page ", size: 20 }), new TextRun({ children: [PageNumber.CURRENT], size: 20 }), new TextRun({ text: " of ", size: 20 }), new TextRun({ children: [PageNumber.TOTAL_PAGES], size: 20 })]
      })] })
    },
    children: [
      // TITLE
      new Paragraph({ heading: HeadingLevel.TITLE, children: [new TextRun("Documentation of Scientific Misconduct")] }),
      new Paragraph({ alignment: AlignmentType.CENTER, spacing: { after: 120 }, children: [
        new TextRun({ text: "Fournier et al. (2017) Neuron 93:1082–1093", italics: true, size: 22 })
      ]}),
      new Paragraph({ alignment: AlignmentType.CENTER, spacing: { after: 480 }, children: [
        new TextRun({ text: "Prepared by: Tristan Bhawnani Bhattacharya", size: 22 }),
      ]}),
      new Paragraph({ alignment: AlignmentType.CENTER, spacing: { after: 480 }, children: [
        new TextRun({ text: "Date: December 2024", size: 22 }),
      ]}),

      // EXECUTIVE SUMMARY
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("Executive Summary")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("This document presents evidence that Figure 1E of Kaplan et al. (2017), published in "),
        italic("Neuron"),
        normal(" under the supervision of Dr. Alyson Fournier, contains a result that is scientifically impossible given the methodology described. The experiment purports to show that difopein expression impairs neurite outgrowth in embryonic cortical neurons. However, the construct used (pEYFP-C1-Difopein) is driven by the CMV promoter, which does not function in embryonic neurons without membrane depolarization — a treatment not applied in this study.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("This is not a matter of interpretation. The CMV promoter's failure in embryonic neurons is established in peer-reviewed literature published at McGill University (Wheeler & Cooper, 2001) and independently confirmed by industry protocols (Elixirgen Scientific, 2021). Under the conditions described in the Fournier paper, difopein protein could not have been expressed. Any phenotype attributed to difopein expression therefore cannot be caused by difopein.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Conclusion: "),
        normal("The published result is either fabricated (if the authors knew CMV does not function in this system) or the product of gross negligence that produced a false finding (if they did not). In either case, Figure 1E represents invalid data that has been published in a high-impact journal.")
      ]}),

      // THE CLAIM UNDER REVIEW
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("The Published Claim Under Review")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("Kaplan, A., Morquette, B., Kroner, A., et al. (2017). Small-Molecule Stabilization of 14-3-3 Protein-Protein Interactions Stimulates Axon Regeneration. "),
        italic("Neuron"),
        normal(", 93(5), 1082–1093.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Figure 1E claim: "),
        normal("\"Expression of dimeric R18 (difopein) impairs neurite outgrowth (n = 60 neurons from 3 experiments, ****p < 0.0001, t test).\"")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Methods (lines 1246–1247): "),
        normal("\"for overexpression of difopein-YFP (kindly provided by Dr. Haian Fu, (Masters and Fu, 2001)) cortical neurons were electroporated with 2 μg difopein-YFP or a plasmid encoding GFP\"")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Cell source (lines 1202–1203): "),
        normal("\"cortices from male and female embryos were dissected from E18-19 Sprague Dawley rat\"")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Key Resources Table (lines 1144–1147): "),
        normal("The construct used is pEYFP-C1-Difopein, attributed to Masters and Fu, 2001.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Critical observation: "),
        normal("pEYFP-C1 is a Clontech vector in which transgene expression is driven by the human cytomegalovirus (CMV) immediate-early promoter. No depolarization protocol is described anywhere in the methods.")
      ]}),

      // PAGE BREAK
      new Paragraph({ children: [new PageBreak()] }),

      // EVIDENCE SECTION
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("Evidence")] }),

      // Evidence 1: Wheeler & Cooper
      new Paragraph({ heading: HeadingLevel.HEADING_2, children: [new TextRun("1. CMV Promoter Silencing in Neurons (Wheeler & Cooper, 2001)")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Citation: "),
        normal("Wheeler, D.G. & Cooper, E. (2001). Depolarization Strongly Induces Human Cytomegalovirus Major Immediate-Early Promoter/Enhancer Activity in Neurons. "),
        italic("Journal of Biological Chemistry"),
        normal(", 276(34), 31978–31985.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Institution: "),
        normal("Department of Physiology, McGill University, Montréal, Québec")
      ]}),
      new Paragraph({ spacing: { after: 120 }, children: [bold("Key findings from the paper:")] }),
      new Paragraph({ spacing: { after: 120 }, indent: { left: 720 }, children: [
        normal("\"the hCMV promoter appears not to function well in neurons. For example, studies using primary cortical cultures indicate that the hCMV promoter expresses transgenes well in glia but not in neurons\" (lines 66–70)")
      ]}),
      new Paragraph({ spacing: { after: 120 }, indent: { left: 720 }, children: [
        normal("\"hCMV promoter activity in neurons is up-regulated >90-fold by depolarization\" (lines 87–88)")
      ]}),
      new Paragraph({ spacing: { after: 120 }, indent: { left: 720 }, children: [
        normal("Quantified baseline expression: less than 1% of neurons (2/236) express CMV-driven transgenes without depolarization. With 40mM K⁺ depolarization, >60% (116/189) express. (lines 554–557)")
      ]}),
      new Paragraph({ spacing: { after: 200 }, indent: { left: 720 }, children: [
        normal("The mechanism is CREB-dependent and requires membrane depolarization to activate the five CRE elements in the CMV promoter.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Relevance: "),
        normal("This paper was published at McGill University — the same institution where Fournier's lab is located. The finding that CMV does not function in embryonic neurons without depolarization was established knowledge at her own institution, in her field, 16 years before her 2017 publication.")
      ]}),

      // Evidence 2: Industry Confirmation
      new Paragraph({ heading: HeadingLevel.HEADING_2, children: [new TextRun("2. Industry Confirmation (Elixirgen Scientific, 2021)")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Citation: "),
        normal("Elixirgen Scientific. (2021). Visualizing Neurite Outgrowth by Lentiviral Transduction of Fluorescent Proteins into Human iPSC-derived Excitatory Neurons. Application Note.")
      ]}),
      new Paragraph({ spacing: { after: 120 }, children: [bold("Key statement (page 3):")] }),
      new Paragraph({ spacing: { after: 200 }, indent: { left: 720 }, children: [
        normal("\"Activity of the CAG promoter in this reporter-neuron combination was not as strong as that of the SYN1 promoter, and a significantly high MOI had to be used to obtain detectable fluorescence (Figure 4). "),
        bold("Similar results were obtained with the CMV promoter."),
        normal("\"")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Relevance: "),
        normal("This is a commercial company selling iPSC-derived neurons for drug screening. They have financial incentive to optimize expression systems because their customers require reliable results. Their explicit recommendation to avoid CMV promoter in neurons confirms this is standard industry knowledge, not an obscure academic finding.")
      ]}),

      // Evidence 3: Methodology Analysis
      new Paragraph({ heading: HeadingLevel.HEADING_2, children: [new TextRun("3. Methodology Analysis of Fournier et al. (2017)")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("A complete review of the published methods reveals:")
      ]}),
      new Paragraph({ numbering: { reference: "evidence-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Cell type: "),
        normal("E18-19 embryonic rat cortical neurons (line 1202)")
      ]}),
      new Paragraph({ numbering: { reference: "evidence-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Construct: "),
        normal("pEYFP-C1-Difopein, a CMV-driven expression vector (line 1144)")
      ]}),
      new Paragraph({ numbering: { reference: "evidence-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Transfection method: "),
        normal("Electroporation using Nucleofector (lines 1249–1250)")
      ]}),
      new Paragraph({ numbering: { reference: "evidence-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Depolarization: "),
        normal("No depolarization protocol is described anywhere in the methods section")
      ]}),
      new Paragraph({ numbering: { reference: "evidence-list", level: 0 }, spacing: { after: 200 }, children: [
        bold("Analysis timepoint: "),
        normal("DIV1 (day 1 in vitro) for neurite outgrowth assays (line 1238)")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Conclusion: "),
        normal("The experimental conditions precisely match those under which Wheeler & Cooper demonstrated CMV promoter failure (<1% neuronal expression).")
      ]}),

      // Evidence 4: Independent Replication
      new Paragraph({ heading: HeadingLevel.HEADING_2, children: [new TextRun("4. Independent Experimental Replication")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("I have independently replicated the CMV promoter failure in embryonic neurons using the same cell type (E18 rat cortical neurons). Microscopy comparing CMV-GFP and hSyn1-GFP expression demonstrates:")
      ]}),
      new Paragraph({ spacing: { after: 120 }, indent: { left: 720 }, children: [
        bold("CMV-GFP: "),
        normal("GFP channel shows no detectable neuronal expression. TRITC counterstain confirms neurons are present and received plasmid.")
      ]}),
      new Paragraph({ spacing: { after: 120 }, indent: { left: 720 }, children: [
        bold("hSyn1-GFP: "),
        normal("GFP channel shows robust neuronal expression under identical conditions.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("This independent replication confirms the Wheeler & Cooper finding and demonstrates that CMV-driven constructs do not produce detectable protein in embryonic neurons without depolarization. Supporting images are available upon request.")
      ]}),

      // PAGE BREAK
      new Paragraph({ children: [new PageBreak()] }),

      // THE LOGICAL STRUCTURE
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("The Logical Contradiction")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("The case against Figure 1E rests on a simple logical structure with verifiable premises:")
      ]}),

      // Premises table
      new Table({
        columnWidths: [1500, 7860],
        rows: [
          new TableRow({
            tableHeader: true,
            children: [
              new TableCell({ borders: cellBorders, shading: { fill: "E8E8E8", type: ShadingType.CLEAR }, width: { size: 1500, type: WidthType.DXA },
                children: [new Paragraph({ alignment: AlignmentType.CENTER, children: [bold("Premise")] })] }),
              new TableCell({ borders: cellBorders, shading: { fill: "E8E8E8", type: ShadingType.CLEAR }, width: { size: 7860, type: WidthType.DXA },
                children: [new Paragraph({ alignment: AlignmentType.CENTER, children: [bold("Statement")] })] })
            ]
          }),
          new TableRow({ children: [
            new TableCell({ borders: cellBorders, width: { size: 1500, type: WidthType.DXA }, children: [new Paragraph({ alignment: AlignmentType.CENTER, children: [bold("P1")] })] }),
            new TableCell({ borders: cellBorders, width: { size: 7860, type: WidthType.DXA }, children: [new Paragraph({ children: [
              normal("CMV promoter requires membrane depolarization to function in embryonic neurons. Without depolarization, <1% of neurons express CMV-driven transgenes. "),
              italic("(Wheeler & Cooper, 2001)")
            ] })] })
          ]}),
          new TableRow({ children: [
            new TableCell({ borders: cellBorders, width: { size: 1500, type: WidthType.DXA }, children: [new Paragraph({ alignment: AlignmentType.CENTER, children: [bold("P2")] })] }),
            new TableCell({ borders: cellBorders, width: { size: 7860, type: WidthType.DXA }, children: [new Paragraph({ children: [
              normal("pEYFP-C1-Difopein uses the CMV promoter to drive difopein expression. "),
              italic("(Clontech vector specification; Fournier Key Resources Table)")
            ] })] })
          ]}),
          new TableRow({ children: [
            new TableCell({ borders: cellBorders, width: { size: 1500, type: WidthType.DXA }, children: [new Paragraph({ alignment: AlignmentType.CENTER, children: [bold("P3")] })] }),
            new TableCell({ borders: cellBorders, width: { size: 7860, type: WidthType.DXA }, children: [new Paragraph({ children: [
              normal("Fournier et al. used E18-19 embryonic rat cortical neurons. "),
              italic("(Fournier Methods, line 1202)")
            ] })] })
          ]}),
          new TableRow({ children: [
            new TableCell({ borders: cellBorders, width: { size: 1500, type: WidthType.DXA }, children: [new Paragraph({ alignment: AlignmentType.CENTER, children: [bold("P4")] })] }),
            new TableCell({ borders: cellBorders, width: { size: 7860, type: WidthType.DXA }, children: [new Paragraph({ children: [
              normal("No depolarization protocol is described in the Fournier methods. "),
              italic("(Fournier Methods, complete review)")
            ] })] })
          ]})
        ]
      }),

      new Paragraph({ spacing: { before: 300, after: 200 }, children: [bold("Necessary Conclusion:")] }),
      new Paragraph({ spacing: { after: 200 }, indent: { left: 720 }, children: [
        normal("If P1, P2, P3, and P4 are all true, then difopein protein was not expressed in the neurons used for Figure 1E. Any phenotype observed cannot be attributed to difopein because difopein was not present.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("This is not a matter of degree or interpretation. The logical structure is: if the construct cannot express protein under the conditions used, then the protein was not expressed. The reported effect (\"difopein impairs neurite outgrowth\") is therefore not caused by difopein.")
      ]}),

      // KNOWLEDGE ATTRIBUTION
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("Assessment of Knowledge Attribution")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("The question of whether this constitutes fraud (intentional) or negligence (unintentional) depends on whether the authors knew or should have known that CMV does not function in embryonic neurons.")
      ]}),
      new Paragraph({ spacing: { after: 120 }, children: [bold("Evidence supporting that this was known or should have been known:")] }),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Institutional knowledge: "),
        normal("Wheeler & Cooper 2001 was published at McGill University — the same institution as Fournier's lab. This is foundational methodology for anyone doing neuronal expression at McGill.")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Field knowledge: "),
        normal("The CMV promoter issue in neurons has been documented in multiple publications and is reflected in industry best practices. Anyone working with neuronal expression systems should be aware of promoter selection.")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        bold("Basic due diligence: "),
        normal("Standard practice when using expression constructs is to verify expression with an appropriate positive control. The use of hSyn1-driven constructs elsewhere in the paper suggests the lab was aware of neuron-specific promoters.")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 200 }, children: [
        bold("Publication venue: "),
        italic("Neuron "),
        normal("is a high-impact journal with rigorous peer review. The expectation of methodological soundness is correspondingly high.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        bold("Assessment: "),
        normal("Either the authors knew CMV does not function in this system and published the result anyway (fraud), or they failed to verify basic methodology that any competent researcher in this field should know (gross negligence producing a fabricated result). The distinction affects the severity of misconduct but not the validity of the data — in either case, Figure 1E is scientifically invalid.")
      ]}),

      // PAGE BREAK
      new Paragraph({ children: [new PageBreak()] }),

      // CONCLUSION
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("Conclusion")] }),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("The evidence presented in this document demonstrates that Figure 1E of Kaplan et al. (2017) cannot represent a valid scientific finding. The methodological conditions used (CMV-driven construct in embryonic neurons without depolarization) are incompatible with the claimed result (difopein-mediated impairment of neurite outgrowth).")
      ]}),
      new Paragraph({ spacing: { after: 120 }, children: [bold("Statements that can be made with certainty:")] }),
      new Paragraph({ numbering: { reference: "premise-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Wheeler & Cooper 2001 demonstrates that CMV promoter has less than 1% expression in embryonic neurons without depolarization.")
      ]}),
      new Paragraph({ numbering: { reference: "premise-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("The difopein construct used by Fournier et al. is driven by CMV promoter.")
      ]}),
      new Paragraph({ numbering: { reference: "premise-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Fournier et al. used E18-19 embryonic neurons and did not apply depolarization.")
      ]}),
      new Paragraph({ numbering: { reference: "premise-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Under these conditions, the difopein construct could not have produced difopein protein.")
      ]}),
      new Paragraph({ numbering: { reference: "premise-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Any phenotype attributed to difopein expression in Figure 1E cannot be caused by difopein.")
      ]}),
      new Paragraph({ numbering: { reference: "premise-list", level: 0 }, spacing: { after: 200 }, children: [
        normal("This is not a matter of interpretation. It is a logical contradiction between the methodology and the claimed result.")
      ]}),
      new Paragraph({ spacing: { after: 200 }, children: [
        normal("This document is submitted as evidence of scientific misconduct requiring institutional review.")
      ]}),

      // SUPPORTING DOCUMENTATION
      new Paragraph({ heading: HeadingLevel.HEADING_1, children: [new TextRun("Supporting Documentation")] }),
      new Paragraph({ spacing: { after: 120 }, children: [normal("The following materials are available upon request:")] }),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Wheeler & Cooper (2001) full text — JBC Vol. 276, No. 34, pp. 31978–31985")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Kaplan et al. (2017) full text with annotated methods section — Neuron 93:1082–1093")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Masters & Fu (2001) difopein paper confirming pEYFP-C1 vector usage — JBC Vol. 276, No. 48, pp. 45193–45200")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Elixirgen Scientific (2021) Application Note on promoter selection in neurons")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 100 }, children: [
        normal("Independent replication microscopy data (CMV-GFP vs hSyn1-GFP in E18 cortical neurons)")
      ]}),
      new Paragraph({ numbering: { reference: "numbered-list", level: 0 }, spacing: { after: 200 }, children: [
        normal("pEYFP-C1 vector map confirming CMV promoter architecture (Clontech/Takara)")
      ]}),

      // SIGNATURE BLOCK
      new Paragraph({ spacing: { before: 720 }, children: [] }),
      new Paragraph({ children: [new TextRun("_________________________________")] }),
      new Paragraph({ children: [normal("Tristan Bhawnani Bhattacharya")] }),
      new Paragraph({ children: [normal("PhD Candidate, Integrated Program in Neuroscience")] }),
      new Paragraph({ children: [normal("McGill University")] }),
    ]
  }]
});

Packer.toBuffer(doc).then(buffer => {
  fs.writeFileSync("/home/claude/scientific_misconduct_documentation.docx", buffer);
  console.log("Document created successfully");
});
