import re
import os
from os.path import join
from lxml import etree

for filename in os.listdir("html/Coupled_Simulation"):
	if not filename.endswith("html") or filename.startswith("index"):
		continue
	print(filename)
	xml = etree.parse(join("html/Coupled_Simulation/", filename))

	defs = xml.xpath("//*[text()='locale' or text()='definition' or text()='inductive' or text()='coinductive'  or text()='lemma'  or text()='theorem'  or text()='corollary' or text()='abbreviation']/..")
	for d in defs:
		nameNode = d.getnext().getnext()
		print(nameNode.text)
		nameNode.set('id', nameNode.text)
	
	with open(join("html/Coupled_Simulation/", filename), "w") as xmlOut:
  		xmlOut.write(etree.tostring(xml, encoding='utf-8', pretty_print=True))
