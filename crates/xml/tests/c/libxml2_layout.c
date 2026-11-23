/* The struct layouts of libxml2 2.15.4's headers against those of
 * verilith-xml's libxml2 ABI (vxml_libxml2_layout): sizes and every field's
 * offset. Built by scripts/test-libxml2.sh with libxml2's own headers.
 * Generated from src/api/libxml2/mod.rs's layout table. */
#include <stddef.h>
#include <stdio.h>
#include <libxml/parser.h>
#include <libxml/parserInternals.h>
#include <libxml/tree.h>
#include <libxml/entities.h>
#include <libxml/valid.h>
#include <libxml/xmlerror.h>

int vxml_libxml2_layout(int which, size_t *out, int max);

static int bad;

static void check(int which, const char *name, const size_t *want, const char *const *fields, int n) {
    size_t got[256];
    int m = vxml_libxml2_layout(which, got, 256);
    if (m != n) { printf("%s: %d entries, want %d\n", name, m, n); bad = 1; return; }
    for (int i = 0; i < n; i++)
        if (got[i] != want[i]) {
            printf("%s.%s: %zu, libxml2 has %zu\n", name, i ? fields[i] : "(size)", got[i], want[i]);
            bad = 1;
        }
}

int main(void) {
    {
        static const size_t want[] = {sizeof(xmlNs), offsetof(xmlNs, next), offsetof(xmlNs, type), offsetof(xmlNs, href), offsetof(xmlNs, prefix), offsetof(xmlNs, _private), offsetof(xmlNs, context)};
        static const char *const fields[] = {"", "next", "type", "href", "prefix", "_private", "context"};
        check(0, "xmlNs", want, fields, 7);
    }
    {
        static const size_t want[] = {sizeof(xmlNode), offsetof(xmlNode, _private), offsetof(xmlNode, type), offsetof(xmlNode, name), offsetof(xmlNode, children), offsetof(xmlNode, last), offsetof(xmlNode, parent), offsetof(xmlNode, next), offsetof(xmlNode, prev), offsetof(xmlNode, doc), offsetof(xmlNode, ns), offsetof(xmlNode, content), offsetof(xmlNode, properties), offsetof(xmlNode, nsDef), offsetof(xmlNode, psvi), offsetof(xmlNode, line), offsetof(xmlNode, extra)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "ns", "content", "properties", "nsDef", "psvi", "line", "extra"};
        check(1, "xmlNode", want, fields, 17);
    }
    {
        static const size_t want[] = {sizeof(xmlAttr), offsetof(xmlAttr, _private), offsetof(xmlAttr, type), offsetof(xmlAttr, name), offsetof(xmlAttr, children), offsetof(xmlAttr, last), offsetof(xmlAttr, parent), offsetof(xmlAttr, next), offsetof(xmlAttr, prev), offsetof(xmlAttr, doc), offsetof(xmlAttr, ns), offsetof(xmlAttr, atype), offsetof(xmlAttr, psvi), offsetof(xmlAttr, id)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "ns", "atype", "psvi", "id"};
        check(2, "xmlAttr", want, fields, 14);
    }
    {
        static const size_t want[] = {sizeof(xmlDoc), offsetof(xmlDoc, _private), offsetof(xmlDoc, type), offsetof(xmlDoc, name), offsetof(xmlDoc, children), offsetof(xmlDoc, last), offsetof(xmlDoc, parent), offsetof(xmlDoc, next), offsetof(xmlDoc, prev), offsetof(xmlDoc, doc), offsetof(xmlDoc, compression), offsetof(xmlDoc, standalone), offsetof(xmlDoc, intSubset), offsetof(xmlDoc, extSubset), offsetof(xmlDoc, oldNs), offsetof(xmlDoc, version), offsetof(xmlDoc, encoding), offsetof(xmlDoc, ids), offsetof(xmlDoc, refs), offsetof(xmlDoc, URL), offsetof(xmlDoc, charset), offsetof(xmlDoc, dict), offsetof(xmlDoc, psvi), offsetof(xmlDoc, parseFlags), offsetof(xmlDoc, properties)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "compression", "standalone", "intSubset", "extSubset", "oldNs", "version", "encoding", "ids", "refs", "URL", "charset", "dict", "psvi", "parseFlags", "properties"};
        check(3, "xmlDoc", want, fields, 25);
    }
    {
        static const size_t want[] = {sizeof(xmlDtd), offsetof(xmlDtd, _private), offsetof(xmlDtd, type), offsetof(xmlDtd, name), offsetof(xmlDtd, children), offsetof(xmlDtd, last), offsetof(xmlDtd, parent), offsetof(xmlDtd, next), offsetof(xmlDtd, prev), offsetof(xmlDtd, doc), offsetof(xmlDtd, notations), offsetof(xmlDtd, elements), offsetof(xmlDtd, attributes), offsetof(xmlDtd, entities), offsetof(xmlDtd, ExternalID), offsetof(xmlDtd, SystemID), offsetof(xmlDtd, pentities)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "notations", "elements", "attributes", "entities", "ExternalID", "SystemID", "pentities"};
        check(4, "xmlDtd", want, fields, 17);
    }
    {
        static const size_t want[] = {sizeof(xmlEntity), offsetof(xmlEntity, _private), offsetof(xmlEntity, type), offsetof(xmlEntity, name), offsetof(xmlEntity, children), offsetof(xmlEntity, last), offsetof(xmlEntity, parent), offsetof(xmlEntity, next), offsetof(xmlEntity, prev), offsetof(xmlEntity, doc), offsetof(xmlEntity, orig), offsetof(xmlEntity, content), offsetof(xmlEntity, length), offsetof(xmlEntity, etype), offsetof(xmlEntity, ExternalID), offsetof(xmlEntity, SystemID), offsetof(xmlEntity, nexte), offsetof(xmlEntity, URI), offsetof(xmlEntity, owner), offsetof(xmlEntity, flags), offsetof(xmlEntity, expandedSize)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "orig", "content", "length", "etype", "ExternalID", "SystemID", "nexte", "URI", "owner", "flags", "expandedSize"};
        check(5, "xmlEntity", want, fields, 21);
    }
    {
        static const size_t want[] = {sizeof(xmlElement), offsetof(xmlElement, _private), offsetof(xmlElement, type), offsetof(xmlElement, name), offsetof(xmlElement, children), offsetof(xmlElement, last), offsetof(xmlElement, parent), offsetof(xmlElement, next), offsetof(xmlElement, prev), offsetof(xmlElement, doc), offsetof(xmlElement, etype), offsetof(xmlElement, content), offsetof(xmlElement, attributes), offsetof(xmlElement, prefix), offsetof(xmlElement, contModel)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "etype", "content", "attributes", "prefix", "contModel"};
        check(6, "xmlElement", want, fields, 15);
    }
    {
        static const size_t want[] = {sizeof(xmlAttribute), offsetof(xmlAttribute, _private), offsetof(xmlAttribute, type), offsetof(xmlAttribute, name), offsetof(xmlAttribute, children), offsetof(xmlAttribute, last), offsetof(xmlAttribute, parent), offsetof(xmlAttribute, next), offsetof(xmlAttribute, prev), offsetof(xmlAttribute, doc), offsetof(xmlAttribute, nexth), offsetof(xmlAttribute, atype), offsetof(xmlAttribute, def), offsetof(xmlAttribute, defaultValue), offsetof(xmlAttribute, tree), offsetof(xmlAttribute, prefix), offsetof(xmlAttribute, elem)};
        static const char *const fields[] = {"", "_private", "type", "name", "children", "last", "parent", "next", "prev", "doc", "nexth", "atype", "def", "defaultValue", "tree", "prefix", "elem"};
        check(7, "xmlAttribute", want, fields, 17);
    }
    {
        static const size_t want[] = {sizeof(xmlElementContent), offsetof(xmlElementContent, type), offsetof(xmlElementContent, ocur), offsetof(xmlElementContent, name), offsetof(xmlElementContent, c1), offsetof(xmlElementContent, c2), offsetof(xmlElementContent, parent), offsetof(xmlElementContent, prefix)};
        static const char *const fields[] = {"", "type", "ocur", "name", "c1", "c2", "parent", "prefix"};
        check(8, "xmlElementContent", want, fields, 8);
    }
    {
        static const size_t want[] = {sizeof(xmlEnumeration), offsetof(xmlEnumeration, next), offsetof(xmlEnumeration, name)};
        static const char *const fields[] = {"", "next", "name"};
        check(9, "xmlEnumeration", want, fields, 3);
    }
    {
        static const size_t want[] = {sizeof(xmlNotation), offsetof(xmlNotation, name), offsetof(xmlNotation, PublicID), offsetof(xmlNotation, SystemID)};
        static const char *const fields[] = {"", "name", "PublicID", "SystemID"};
        check(10, "xmlNotation", want, fields, 4);
    }
    {
        static const size_t want[] = {sizeof(xmlBuffer), offsetof(xmlBuffer, content), offsetof(xmlBuffer, use), offsetof(xmlBuffer, size), offsetof(xmlBuffer, alloc), offsetof(xmlBuffer, contentIO)};
        static const char *const fields[] = {"", "content", "use", "size", "alloc", "contentIO"};
        check(11, "xmlBuffer", want, fields, 6);
    }
    {
        static const size_t want[] = {sizeof(xmlError), offsetof(xmlError, domain), offsetof(xmlError, code), offsetof(xmlError, message), offsetof(xmlError, level), offsetof(xmlError, file), offsetof(xmlError, line), offsetof(xmlError, str1), offsetof(xmlError, str2), offsetof(xmlError, str3), offsetof(xmlError, int1), offsetof(xmlError, int2), offsetof(xmlError, ctxt), offsetof(xmlError, node)};
        static const char *const fields[] = {"", "domain", "code", "message", "level", "file", "line", "str1", "str2", "str3", "int1", "int2", "ctxt", "node"};
        check(12, "xmlError", want, fields, 14);
    }
    {
        static const size_t want[] = {sizeof(xmlSAXHandler), offsetof(xmlSAXHandler, internalSubset), offsetof(xmlSAXHandler, isStandalone), offsetof(xmlSAXHandler, hasInternalSubset), offsetof(xmlSAXHandler, hasExternalSubset), offsetof(xmlSAXHandler, resolveEntity), offsetof(xmlSAXHandler, getEntity), offsetof(xmlSAXHandler, entityDecl), offsetof(xmlSAXHandler, notationDecl), offsetof(xmlSAXHandler, attributeDecl), offsetof(xmlSAXHandler, elementDecl), offsetof(xmlSAXHandler, unparsedEntityDecl), offsetof(xmlSAXHandler, setDocumentLocator), offsetof(xmlSAXHandler, startDocument), offsetof(xmlSAXHandler, endDocument), offsetof(xmlSAXHandler, startElement), offsetof(xmlSAXHandler, endElement), offsetof(xmlSAXHandler, reference), offsetof(xmlSAXHandler, characters), offsetof(xmlSAXHandler, ignorableWhitespace), offsetof(xmlSAXHandler, processingInstruction), offsetof(xmlSAXHandler, comment), offsetof(xmlSAXHandler, warning), offsetof(xmlSAXHandler, error), offsetof(xmlSAXHandler, fatalError), offsetof(xmlSAXHandler, getParameterEntity), offsetof(xmlSAXHandler, cdataBlock), offsetof(xmlSAXHandler, externalSubset), offsetof(xmlSAXHandler, initialized), offsetof(xmlSAXHandler, _private), offsetof(xmlSAXHandler, startElementNs), offsetof(xmlSAXHandler, endElementNs), offsetof(xmlSAXHandler, serror)};
        static const char *const fields[] = {"", "internalSubset", "isStandalone", "hasInternalSubset", "hasExternalSubset", "resolveEntity", "getEntity", "entityDecl", "notationDecl", "attributeDecl", "elementDecl", "unparsedEntityDecl", "setDocumentLocator", "startDocument", "endDocument", "startElement", "endElement", "reference", "characters", "ignorableWhitespace", "processingInstruction", "comment", "warning", "error", "fatalError", "getParameterEntity", "cdataBlock", "externalSubset", "initialized", "_private", "startElementNs", "endElementNs", "serror"};
        check(13, "xmlSAXHandler", want, fields, 33);
    }
    {
        static const size_t want[] = {sizeof(xmlParserInput), offsetof(xmlParserInput, buf), offsetof(xmlParserInput, filename), offsetof(xmlParserInput, directory), offsetof(xmlParserInput, base), offsetof(xmlParserInput, cur), offsetof(xmlParserInput, end), offsetof(xmlParserInput, length), offsetof(xmlParserInput, line), offsetof(xmlParserInput, col), offsetof(xmlParserInput, consumed), offsetof(xmlParserInput, free), offsetof(xmlParserInput, encoding), offsetof(xmlParserInput, version), offsetof(xmlParserInput, flags), offsetof(xmlParserInput, id), offsetof(xmlParserInput, parentConsumed), offsetof(xmlParserInput, entity)};
        static const char *const fields[] = {"", "buf", "filename", "directory", "base", "cur", "end", "length", "line", "col", "consumed", "free", "encoding", "version", "flags", "id", "parentConsumed", "entity"};
        check(14, "xmlParserInput", want, fields, 18);
    }
    {
        static const size_t want[] = {sizeof(xmlParserCtxt), offsetof(xmlParserCtxt, sax), offsetof(xmlParserCtxt, userData), offsetof(xmlParserCtxt, myDoc), offsetof(xmlParserCtxt, wellFormed), offsetof(xmlParserCtxt, replaceEntities), offsetof(xmlParserCtxt, version), offsetof(xmlParserCtxt, encoding), offsetof(xmlParserCtxt, standalone), offsetof(xmlParserCtxt, html), offsetof(xmlParserCtxt, input), offsetof(xmlParserCtxt, inputNr), offsetof(xmlParserCtxt, inputMax), offsetof(xmlParserCtxt, inputTab), offsetof(xmlParserCtxt, node), offsetof(xmlParserCtxt, nodeNr), offsetof(xmlParserCtxt, nodeMax), offsetof(xmlParserCtxt, nodeTab), offsetof(xmlParserCtxt, record_info), offsetof(xmlParserCtxt, node_seq), offsetof(xmlParserCtxt, errNo), offsetof(xmlParserCtxt, hasExternalSubset), offsetof(xmlParserCtxt, hasPErefs), offsetof(xmlParserCtxt, external), offsetof(xmlParserCtxt, valid), offsetof(xmlParserCtxt, validate), offsetof(xmlParserCtxt, vctxt), offsetof(xmlParserCtxt, instate), offsetof(xmlParserCtxt, token), offsetof(xmlParserCtxt, directory), offsetof(xmlParserCtxt, name), offsetof(xmlParserCtxt, nameNr), offsetof(xmlParserCtxt, nameMax), offsetof(xmlParserCtxt, nameTab), offsetof(xmlParserCtxt, nbChars), offsetof(xmlParserCtxt, checkIndex), offsetof(xmlParserCtxt, keepBlanks), offsetof(xmlParserCtxt, disableSAX), offsetof(xmlParserCtxt, inSubset), offsetof(xmlParserCtxt, intSubName), offsetof(xmlParserCtxt, extSubURI), offsetof(xmlParserCtxt, extSubSystem), offsetof(xmlParserCtxt, space), offsetof(xmlParserCtxt, spaceNr), offsetof(xmlParserCtxt, spaceMax), offsetof(xmlParserCtxt, spaceTab), offsetof(xmlParserCtxt, depth), offsetof(xmlParserCtxt, entity), offsetof(xmlParserCtxt, charset), offsetof(xmlParserCtxt, nodelen), offsetof(xmlParserCtxt, nodemem), offsetof(xmlParserCtxt, pedantic), offsetof(xmlParserCtxt, _private), offsetof(xmlParserCtxt, loadsubset), offsetof(xmlParserCtxt, linenumbers), offsetof(xmlParserCtxt, catalogs), offsetof(xmlParserCtxt, recovery), offsetof(xmlParserCtxt, progressive), offsetof(xmlParserCtxt, dict), offsetof(xmlParserCtxt, atts), offsetof(xmlParserCtxt, maxatts), offsetof(xmlParserCtxt, docdict), offsetof(xmlParserCtxt, str_xml), offsetof(xmlParserCtxt, str_xmlns), offsetof(xmlParserCtxt, str_xml_ns), offsetof(xmlParserCtxt, sax2), offsetof(xmlParserCtxt, nsNr), offsetof(xmlParserCtxt, nsMax), offsetof(xmlParserCtxt, nsTab), offsetof(xmlParserCtxt, attallocs), offsetof(xmlParserCtxt, pushTab), offsetof(xmlParserCtxt, attsDefault), offsetof(xmlParserCtxt, attsSpecial), offsetof(xmlParserCtxt, nsWellFormed), offsetof(xmlParserCtxt, options), offsetof(xmlParserCtxt, dictNames), offsetof(xmlParserCtxt, freeElemsNr), offsetof(xmlParserCtxt, freeElems), offsetof(xmlParserCtxt, freeAttrsNr), offsetof(xmlParserCtxt, freeAttrs), offsetof(xmlParserCtxt, lastError), offsetof(xmlParserCtxt, parseMode), offsetof(xmlParserCtxt, nbentities), offsetof(xmlParserCtxt, sizeentities), offsetof(xmlParserCtxt, nodeInfo), offsetof(xmlParserCtxt, nodeInfoNr), offsetof(xmlParserCtxt, nodeInfoMax), offsetof(xmlParserCtxt, nodeInfoTab), offsetof(xmlParserCtxt, input_id), offsetof(xmlParserCtxt, sizeentcopy), offsetof(xmlParserCtxt, endCheckState), offsetof(xmlParserCtxt, nbErrors), offsetof(xmlParserCtxt, nbWarnings), offsetof(xmlParserCtxt, maxAmpl), offsetof(xmlParserCtxt, nsdb), offsetof(xmlParserCtxt, attrHashMax), offsetof(xmlParserCtxt, attrHash), offsetof(xmlParserCtxt, errorHandler), offsetof(xmlParserCtxt, errorCtxt), offsetof(xmlParserCtxt, resourceLoader), offsetof(xmlParserCtxt, resourceCtxt), offsetof(xmlParserCtxt, convImpl), offsetof(xmlParserCtxt, convCtxt)};
        static const char *const fields[] = {"", "sax", "userData", "myDoc", "wellFormed", "replaceEntities", "version", "encoding", "standalone", "html", "input", "inputNr", "inputMax", "inputTab", "node", "nodeNr", "nodeMax", "nodeTab", "record_info", "node_seq", "errNo", "hasExternalSubset", "hasPErefs", "external", "valid", "validate", "vctxt", "instate", "token", "directory", "name", "nameNr", "nameMax", "nameTab", "nbChars", "checkIndex", "keepBlanks", "disableSAX", "inSubset", "intSubName", "extSubURI", "extSubSystem", "space", "spaceNr", "spaceMax", "spaceTab", "depth", "entity", "charset", "nodelen", "nodemem", "pedantic", "_private", "loadsubset", "linenumbers", "catalogs", "recovery", "progressive", "dict", "atts", "maxatts", "docdict", "str_xml", "str_xmlns", "str_xml_ns", "sax2", "nsNr", "nsMax", "nsTab", "attallocs", "pushTab", "attsDefault", "attsSpecial", "nsWellFormed", "options", "dictNames", "freeElemsNr", "freeElems", "freeAttrsNr", "freeAttrs", "lastError", "parseMode", "nbentities", "sizeentities", "nodeInfo", "nodeInfoNr", "nodeInfoMax", "nodeInfoTab", "input_id", "sizeentcopy", "endCheckState", "nbErrors", "nbWarnings", "maxAmpl", "nsdb", "attrHashMax", "attrHash", "errorHandler", "errorCtxt", "resourceLoader", "resourceCtxt", "convImpl", "convCtxt"};
        check(15, "xmlParserCtxt", want, fields, 103);
    }
    {
        static const size_t want[] = {sizeof(xmlSAXLocator), offsetof(xmlSAXLocator, getPublicId), offsetof(xmlSAXLocator, getSystemId), offsetof(xmlSAXLocator, getLineNumber), offsetof(xmlSAXLocator, getColumnNumber)};
        static const char *const fields[] = {"", "getPublicId", "getSystemId", "getLineNumber", "getColumnNumber"};
        check(16, "xmlSAXLocator", want, fields, 5);
    }
    {
        static const size_t want[] = {sizeof(xmlID), offsetof(xmlID, next), offsetof(xmlID, value), offsetof(xmlID, attr), offsetof(xmlID, name), offsetof(xmlID, lineno), offsetof(xmlID, doc)};
        static const char *const fields[] = {"", "next", "value", "attr", "name", "lineno", "doc"};
        check(17, "xmlID", want, fields, 7);
    }
    if (!bad) printf("libxml2 layouts: %d structs match\n", 18);
    return bad;
}
