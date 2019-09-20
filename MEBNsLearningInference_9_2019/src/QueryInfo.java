

import java.io.Serializable;
import java.util.List;

public class QueryInfo implements Serializable {
	
	private List<Integer> shipIDs;
	private List<EvidenceInfo> evidenceList;
	
	public QueryInfo() {
		
	}
	
	public QueryInfo(List<Integer> shipIDs, List<EvidenceInfo> evidenceList) {
		this.shipIDs = shipIDs;
		this.evidenceList = evidenceList;
	}


	public List<EvidenceInfo> getEvidenceList() {
		return evidenceList;
	}

	public void setEvidenceList(List<EvidenceInfo> evidenceList) {
		this.evidenceList = evidenceList;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		try {
			String ret = "[ShipIDs=" + this.getShipIDs() + "]";
			for (EvidenceInfo evidence : this.getEvidenceList()) {
				ret += ", " + evidence;
			}
			
			return ret;
		} catch (Exception e) {
			// TODO: handle exception
		}
		return super.toString();
	}

	/**
	 * @return the shipIDs
	 */
	public List<Integer> getShipIDs() {
		return shipIDs;
	}

	/**
	 * @param shipIDs the shipIDs to set
	 */
	public void setShipIDs(List<Integer> shipIDs) {
		this.shipIDs = shipIDs;
	}
	
	

}