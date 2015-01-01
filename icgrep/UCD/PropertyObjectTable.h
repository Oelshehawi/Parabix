#ifndef PROPERTYOBJECTTABLE_H
#define PROPERTYOBJECTTABLE_H
/*
 *  Copyright (c) 2014 International Characters, Inc.
 *  This software is licensed to the public under the Open Software License 3.0.
 *  icgrep is a trademark of International Characters, Inc.
 *
 *  This file is generated by UCD_properties.py - manual edits may be lost.
 */

#include "PropertyObjects.h"
#include "PropertyAliases.h"
#include "Blocks.h"
#include "Scripts.h"
#include "ScriptExtensions.h"
#include "DerivedGeneralCategory.h"
#include "PropList.h"
#include "DerivedCoreProperties.h"
#include "LineBreak.h"
#include "EastAsianWidth.h"
#include "HangulSyllableType.h"

namespace UCD {

  PropertyObject* property_object_table[] = {
    new UnsupportedPropertyObject(cjkAccountingNumeric, NumericProperty),
    new UnsupportedPropertyObject(cjkOtherNumeric, NumericProperty),
    new UnsupportedPropertyObject(cjkPrimaryNumeric, NumericProperty),
    new UnsupportedPropertyObject(nv, NumericProperty),
    new UnsupportedPropertyObject(cf, StringProperty),
    new UnsupportedPropertyObject(cjkCompatibilityVariant, StringProperty),
    new UnsupportedPropertyObject(dm, StringProperty),
    new UnsupportedPropertyObject(FC_NFKC, StringProperty),
    new UnsupportedPropertyObject(lc, StringProperty),
    new UnsupportedPropertyObject(NFKC_CF, StringProperty),
    new UnsupportedPropertyObject(scf, CodepointProperty),
    new UnsupportedPropertyObject(slc, CodepointProperty),
    new UnsupportedPropertyObject(stc, CodepointProperty),
    new UnsupportedPropertyObject(suc, CodepointProperty),
    new UnsupportedPropertyObject(tc, StringProperty),
    new UnsupportedPropertyObject(uc, StringProperty),
    new UnsupportedPropertyObject(bmg, MiscellaneousProperty),
    new UnsupportedPropertyObject(bpb, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIICore, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_GSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_HSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_JSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_KPSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_KSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_MSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_TSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_USource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkIRG_VSource, MiscellaneousProperty),
    new UnsupportedPropertyObject(cjkRSUnicode, MiscellaneousProperty),
    new UnsupportedPropertyObject(isc, MiscellaneousProperty),
    new UnsupportedPropertyObject(JSN, MiscellaneousProperty),
    new UnsupportedPropertyObject(na, MiscellaneousProperty),
    new UnsupportedPropertyObject(na1, MiscellaneousProperty),
    new UnsupportedPropertyObject(Name_Alias, MiscellaneousProperty),
    new UnsupportedPropertyObject(scx, MiscellaneousProperty),
    new UnsupportedPropertyObject(age, CatalogProperty),
    &BLK_ns::property_object,
    &SC_ns::property_object,
    new UnsupportedPropertyObject(bc, EnumeratedProperty),
    new UnsupportedPropertyObject(bpt, EnumeratedProperty),
    new UnsupportedPropertyObject(ccc, EnumeratedProperty),
    new UnsupportedPropertyObject(dt, EnumeratedProperty),
    &EA_ns::property_object,
    &GC_ns::property_object,
    new UnsupportedPropertyObject(GCB, EnumeratedProperty),
    &HST_ns::property_object,
    new UnsupportedPropertyObject(InMC, EnumeratedProperty),
    new UnsupportedPropertyObject(InSC, EnumeratedProperty),
    new UnsupportedPropertyObject(jg, EnumeratedProperty),
    new UnsupportedPropertyObject(jt, EnumeratedProperty),
    &LB_ns::property_object,
    new UnsupportedPropertyObject(NFC_QC, EnumeratedProperty),
    new UnsupportedPropertyObject(NFD_QC, EnumeratedProperty),
    new UnsupportedPropertyObject(NFKC_QC, EnumeratedProperty),
    new UnsupportedPropertyObject(NFKD_QC, EnumeratedProperty),
    new UnsupportedPropertyObject(nt, EnumeratedProperty),
    new UnsupportedPropertyObject(SB, EnumeratedProperty),
    new UnsupportedPropertyObject(WB, EnumeratedProperty),
    &AHEX_ns::property_object,
    &ALPHA_ns::property_object,
    &BIDI_C_ns::property_object,
    new UnsupportedPropertyObject(Bidi_M, BinaryProperty),
    &CASED_ns::property_object,
    new UnsupportedPropertyObject(CE, BinaryProperty),
    &CI_ns::property_object,
    new UnsupportedPropertyObject(Comp_Ex, BinaryProperty),
    &CWCF_ns::property_object,
    &CWCM_ns::property_object,
    new UnsupportedPropertyObject(CWKCF, BinaryProperty),
    &CWL_ns::property_object,
    &CWT_ns::property_object,
    &CWU_ns::property_object,
    &DASH_ns::property_object,
    &DEP_ns::property_object,
    &DI_ns::property_object,
    &DIA_ns::property_object,
    &EXT_ns::property_object,
    &GR_BASE_ns::property_object,
    &GR_EXT_ns::property_object,
    &GR_LINK_ns::property_object,
    &HEX_ns::property_object,
    &HYPHEN_ns::property_object,
    &IDC_ns::property_object,
    &IDEO_ns::property_object,
    &IDS_ns::property_object,
    &IDSB_ns::property_object,
    &IDST_ns::property_object,
    &JOIN_C_ns::property_object,
    &LOE_ns::property_object,
    &LOWER_ns::property_object,
    &MATH_ns::property_object,
    &NCHAR_ns::property_object,
    &OALPHA_ns::property_object,
    &ODI_ns::property_object,
    &OGR_EXT_ns::property_object,
    &OIDC_ns::property_object,
    &OIDS_ns::property_object,
    &OLOWER_ns::property_object,
    &OMATH_ns::property_object,
    &OUPPER_ns::property_object,
    &PAT_SYN_ns::property_object,
    &PAT_WS_ns::property_object,
    &QMARK_ns::property_object,
    &RADICAL_ns::property_object,
    &SD_ns::property_object,
    &STERM_ns::property_object,
    &TERM_ns::property_object,
    &UIDEO_ns::property_object,
    &UPPER_ns::property_object,
    &VS_ns::property_object,
    &WSPACE_ns::property_object,
    &XIDC_ns::property_object,
    &XIDS_ns::property_object,
    new UnsupportedPropertyObject(XO_NFC, BinaryProperty),
    new UnsupportedPropertyObject(XO_NFD, BinaryProperty),
    new UnsupportedPropertyObject(XO_NFKC, BinaryProperty),
    new UnsupportedPropertyObject(XO_NFKD, BinaryProperty)  };
}

#endif
